/**
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 */

import {
  type BlockIdExtension,
  blockIdState,
  getPeerDependencyFromEditor,
  registerNodeStructure,
} from '@lexical/extension';
import {
  applyUpdate,
  ContentType,
  createID,
  createRelativePositionFromJSON,
  Doc,
  encodeStateAsUpdate,
  findIndexSS,
  Item,
  iterateStructsByIdSet,
  Node as YNode,
  RelativePosition,
  relativePositionToJSON,
  type Transaction,
  UndoManager,
} from '@y/y';
import {
  $addUpdateTag,
  $createLineBreakNode,
  $createNodeSelection,
  $createRangeSelection,
  $flushSyncAfterUpdate,
  $getNodeByKey,
  $getRoot,
  $getSelection,
  $getState,
  $isElementNode,
  $isNodeSelection,
  $isRangeSelection,
  $isRootNode,
  $isTextNode,
  $onUpdate,
  $setSelection,
  COLLABORATION_TAG,
  DEFER_COMPOSITION_MERGE_TAG,
  type EditorState,
  ElementNode,
  getActiveElement,
  getTransformSetFromKlass,
  HISTORY_MERGE_TAG,
  INTERNAL_$normalizeNodeStructure,
  isCurrentlyReadOnlyMode,
  type Klass,
  type LexicalEditor,
  type LexicalNode,
  LexicalWarning,
  type LineBreakNode,
  type NodeKey,
  type PointType,
  type RangeSelection,
  SELECTION_CHANGE_COMMAND,
  SKIP_COLLAB_TAG,
  SKIP_DOM_SELECTION_TAG,
  TextNode,
  type Transform,
} from 'lexical';

import {$appendAll, ARGUMENTS_CHUNK, pushAll, spliceAll} from './Arrays';
import {type ClientIDRange, constrainClientID} from './ClientID';
import {DEFAULT_ROOT_NAME, LEGACY_ROOTS} from './constants';
import {Hidden, shownLength} from './Hidden';
import {$storedIdNow, $touchChanged, Reader} from './Read';
import {
  $groupFields,
  $isWrapper,
  $setBlockId,
  canStoreAs,
  deriveStorageKind,
  getGroupSpec,
  identityOf,
  klassOf,
  LAYOUT_PREFIX,
  LAYOUT_VERSION,
  MARKER,
  type Pin,
  PIN_PREFIX,
  RUN_END,
  stableStringify,
  type StorageKind,
  storageKindOf,
  withPins,
} from './Schema';
import {$checkWrite, checkContainer} from './SelfCheck';
import {$unstorableSlotHosts} from './Slots';
import {
  type CS,
  isEndItem,
  nameOf,
  prevLiveEnd,
  Roles,
  State,
  typeOf,
} from './State';
import {
  notesSince,
  RECOVERED_READ_WARNING,
  RECOVERED_WRITE_WARNING,
  SELF_CHECK_WARNING,
  STORAGE_MISMATCH_WARNING,
  UNKNOWN_NODE_TYPES_WARNING,
  UNSUPPORTED_CONFIG_WARNING,
  UNSUPPORTED_LAYOUT_WARNING,
  UNSUPPORTED_SLOTS_WARNING,
  type YWarningCode,
} from './Warnings';
import {$holdsLines, type WritePlan, Writer} from './Write';

// A collaborator's change: DEFER_COMPOSITION_MERGE_TAG keeps Lexical from
// merging text into an active IME composition (the composed DOM text node
// would take in the merged text).
const REMOTE_TAGS = [
  COLLABORATION_TAG,
  HISTORY_MERGE_TAG,
  DEFER_COMPOSITION_MERGE_TAG,
];
/** The binding's refresh of derived group fields (see flushRefresh). */
const REFRESH_TAG = 'lexical-y-refresh';
/** The author's normalization of its own update (see normalizeUntransformed). */
const NORMALIZE_TAG = 'lexical-y-normalize';
/**
 * The update Lexical makes to run a newly registered transform over the
 * document, run by the binding on its own (see noteRegistrations).
 */
const REGISTRATION_TAG = 'lexical-y-registration';
/** BlockIdExtension's update that names blocks a commit left without an id. */
const BLOCK_ID_REPAIR_TAG = 'block-id-repair';

/**
 * The binding's own updates that wait for the editor to be idle (see
 * runPending), in the order they run.
 */
type PendingWork = 'hidden' | 'reread' | 'normalize' | 'refresh' | 'register';
const PENDING_ORDER: readonly PendingWork[] = [
  'hidden',
  'reread',
  'normalize',
  'refresh',
  'register',
];

/**
 * How many times in a row the binding reads containers again because a
 * follow-up changed what it does not write, before it gives up (a transform
 * that rewrites the same content every time).
 */
const MAX_REREADS = 3;

/**
 * How many updates for registered transforms the binding runs before the
 * event loop turns (see YBinding#runRegistrationPasses), as Lexical caps
 * the updates its listeners queue in a row. Transforms registered in a row
 * share one (see noteRegistrations): only a listener that registers one
 * after every commit reaches it.
 */
const MAX_REGISTRATION_RUNS = 100;

/** @experimental The state of a {@link YBinding}. */
export type YBindingStatus =
  /** Waiting for the first sync: nothing is written. */
  | 'pending'
  /** Reading and writing. */
  | 'active'
  /**
   * The binding cannot write the document safely: a layout this version
   * does not support, a node type the editor does not register, or a type
   * stored in a way its class cannot be (a warning says which). Read only.
   */
  | 'readonly';

/** @experimental Options of {@link YBinding} (and `YCollabExtension`). */
export interface YBindingOptions {
  /** The shared root to bind; defaults to `doc.get('lexical-y')`. */
  root?: YNode;
  /** Undo capture timeout in ms (default 500); null disables undo. */
  captureTimeout?: number | null;
  /**
   * Called when `status` changes, once the binding's work is done and Yjs is
   * idle (like warnings, never inside a Yjs observer or transaction). Several
   * changes in one such step report the last.
   */
  onStatus?: (status: YBindingStatus) => void;
  /**
   * Read every line a local write touched back from Yjs and compare it with
   * the editor; mismatches are reported to the editor's `onWarn` as a
   * `LexicalWarning` (code `'@lexical/y/self-check'`).
   * Structural changes (and remote changes) also compare a fresh read of
   * the whole container: every time for containers of up to 256 lines and
   * nodes, and with probability 256 / size for bigger ones, so the expected
   * cost of an edit stays bounded. Default: off. A debugging aid: turn it
   * on in tests and development builds to catch binding bugs.
   */
  selfCheck?: boolean;
  /**
   * The fraction of changes the self-check samples (default 1): of local
   * writes, and of remote changes, where a sampled check that finds the
   * editor differing from the shared content also reads those containers
   * again (see `selfCheck`).
   */
  selfCheckSample?: number;
  /**
   * Initialize even when an older layout's root has content: for a
   * converter writing the layout root of an existing document.
   */
  convert?: boolean;
  /**
   * The range of the document's client ids: `'uint53'` (default, Yjs 14's
   * ids, left as they are) or `'uint32'` (kept in 32 bits, for servers on
   * yrs before 0.28; see {@link ClientIDRange}).
   */
  clientIDRange?: ClientIDRange;
}

/**
 * @experimental A selection as Yjs relative positions, from
 * `YBinding#getCursor` (for an awareness-based cursor UI).
 */
export interface YCursor {
  anchor: unknown;
  focus: unknown;
}

/**
 * The layout version `root` records: the highest of its `lexical-y:<n>`
 * attributes (see LAYOUT_PREFIX), null when it has none, and NaN when one is
 * not a version (an integer from 1, set to true), which opens the document
 * read only.
 */
function recordedLayout(root: YNode): number | null {
  let version: number | null = null;
  const attrs = root.getAttrs() as Record<string, unknown>;
  for (const k in attrs) {
    if (k.startsWith(LAYOUT_PREFIX)) {
      const n = k.slice(LAYOUT_PREFIX.length);
      if (!/^[1-9][0-9]*$/.test(n) || attrs[k] !== true) {
        return NaN;
      }
      version = Math.max(version ?? 0, Number(n));
    }
  }
  return version;
}

/**
 * @experimental A Yjs 14 binding for one editor and one shared root.
 *
 * Every container (the root, and every node stored as its own Y.Node) holds
 * one sequence of text, child nodes and line markers; see the package README
 * for the layout.
 *
 * Warnings (read only states, recoveries, the opt-in self-check) go to the
 * editor's `onWarn` as `LexicalWarning`s with `@lexical/y/...` codes (see
 * `UNSUPPORTED_LAYOUT_WARNING` and the other `*_WARNING` constants), once a
 * remote change has been applied in full: never from inside a Yjs observer
 * or transaction. A handler that throws does not affect syncing.
 */
export class YBinding {
  private readonly _editor: LexicalEditor;
  private readonly _doc: Doc;
  private readonly _root: YNode;
  private _status: YBindingStatus = 'pending';
  private readonly _pins = new Map<string, Pin>();
  private _undoManager: UndoManager | null = null;
  private state: State;
  private readonly options: YBindingOptions;
  private disposers: (() => void)[] = [];
  /** Origin of the initialization transaction (not tracked by undo). */
  private readonly initOrigin = {binding: this};
  /** Origin of follow-up writes and pin records (not tracked by undo). */
  private readonly followUpOrigin = {binding: this, followUp: true};
  /**
   * Elements Lexical's transforms ran on since the last commit (see
   * onUpdate).
   */
  private readonly transformed = new Set<NodeKey>();
  /**
   * Elements a local update changed without Lexical's transforms, for the
   * author's normalization (see normalizeUntransformed), with what stores
   * each once it is written (its shared node, or its line's marker): a
   * remote change read before the normalization runs can give the element a
   * new node.
   */
  private readonly untransformed = new Map<NodeKey, YNode | Item | null>();
  /**
   * Text nodes a local update changed without Lexical's transforms, for the
   * author's normalization too (its text transforms: a line feed split into
   * a line break node, as every reader shows it).
   */
  private readonly untransformedText = new Set<NodeKey>();
  /** The binding's own updates waiting for the editor (see runPending). */
  private readonly pending = new Set<PendingWork>();
  /** Whether the author's normalization is queued (see queueNormalize). */
  private normalizeQueued = false;
  /**
   * Groups a local change touched, for the refresh that follows it (see
   * flushRefresh), kept apart from the groups a remote read refreshes at
   * once.
   */
  private readonly localRefresh = new Set<NodeKey>();
  /**
   * Groups a remote read touched while another update was running, for the
   * refresh that follows it once the editor is idle (see flushRefresh).
   */
  private readonly remoteRefresh = new Set<NodeKey>();
  private pendingScheduled = false;
  /**
   * Whether the editor committed in the current task (see commitsAtOnce).
   * An object of its own, cleared by a microtask that keeps only it (see
   * endOfTask).
   */
  private readonly task = {committed: false};
  /**
   * Containers a follow-up changed in ways that are not written (see
   * Writer#followUp): read again, so the editor shows what is stored.
   */
  private readonly refused = new Set<CS>();
  /** Re-reads in a row (see MAX_REREADS). */
  private rereads = 0;
  /**
   * Whether a container in `refused` holds a change of BlockIdExtension's
   * naming update (see rereadRefused).
   */
  private refusedNaming = false;
  /**
   * Block ids whose holders a local write changed and that the editor does
   * not show as a read settles them (see onUpdate): settled in the next
   * re-read, which is not written.
   */
  private readonly toSettle = new Set<string>();
  /**
   * The node transforms each type had at the last commit: a new one (or one
   * registered again) marks every node of its type dirty (see
   * isRegistrationPass).
   */
  /** Types a transform was registered for since the last commit. */
  private readonly registeredTypes = new Set<string>();
  /**
   * The updates Lexical made for transforms registered while the binding
   * writes, taken off Lexical's queue: run once the editor is idle, as an
   * update of their own (see noteRegistrations).
   */
  private readonly registrationPasses: (() => void)[] = [];
  /**
   * Registration passes run since the event loop last turned (see
   * runRegistrationPasses): a listener that registers a transform after
   * every commit would otherwise make them forever, as Lexical stops
   * updates that listeners keep queuing.
   */
  private registrationRuns = 0;
  private readonly transformSets = new Map<
    string,
    ReadonlySet<Transform<LexicalNode>>
  >();
  /**
   * Options of the editor's extensions the binding cannot write safely with
   * (see UNSUPPORTED_CONFIG_WARNING): while there are any, the binding is
   * read only.
   */
  private unsupportedConfig: string[] = [];
  /** A status change not reported to `onStatus` yet (see flushWarnings). */
  private pendingStatus: YBindingStatus | null = null;
  /** How many of the class and value notes this binding has reported. */
  private notesSeen = 0;
  /** Counts remote transactions (a local write's self-check is skipped when one landed during it). */
  private remoteSeq = 0;
  /** Origin of read-only scans (no changes). */
  private readonly scanOrigin = {binding: this, scan: true};
  /** Stored nodes the running undo/redo restores (see isKeptByUndo). */
  private restoring: Set<string> | null = null;
  /** Stored nodes the running undo/redo deletes (it inserted them). */
  private removing: Set<Item> | null = null;
  private wasEditable = true;
  private undoCache = new WeakMap<YNode, Set<number>>();
  private readonly afterTransaction: (tr: Transaction) => void;
  private readonly beforeTransaction: (tr: Transaction) => void;
  private readonly beforeObserverCalls = (tr: Transaction): void => {
    tr.changed.forEach((_subs, type) => {
      if (this.state.containers.has(type) || this.isUnderRoot(type)) {
        type._hasFormatting = false;
      }
    });
  };
  /**
   * Whether a shared type is the binding's root or inside it: a container
   * this client no longer shows (a table it deleted) is still the binding's,
   * and Yjs must not clean up its formats either (see beforeObserverCalls).
   */
  private isUnderRoot(type: YNode): boolean {
    for (let t: YNode | null = type; t !== null; t = t.parent) {
      if (t === this._root) {
        return true;
      }
    }
    return false;
  }
  /** The local selection before the remote transaction being applied. */
  private pendingCursor: YCursor | null = null;
  /**
   * The selection before the local change being written (see onUpdate), for
   * the undo step it starts (see stack-item-added in startInner).
   */
  private writeCursor: YCursor | null = null;
  /** The selection before the last undo or redo (see stack-item-added). */
  private undoneCursor: YCursor | null = null;
  /**
   * While an undo or redo runs: the selection from before the step it
   * reverts, which the read restores (null: map the current one).
   */
  private stepCursor: YCursor | null = null;
  /** The node classes' own transforms (see $refreshGroups), per class. */
  private readonly classTransforms = new Map<
    Klass<LexicalNode>,
    Set<Transform<LexicalNode>>
  >();
  /** Warnings not passed to the editor's onWarn yet (see flushWarnings). */
  private readonly pendingWarnings: LexicalWarning[] = [];
  /** Depth of the binding's own work in progress (see guard). */
  private busy = 0;
  private flushingWarnings = false;
  private readonly afterAllTransactions = (): void => this.flushWarnings();

  /** The bound editor. */
  get editor(): LexicalEditor {
    return this._editor;
  }

  /** The shared document. */
  get doc(): Doc {
    return this._doc;
  }

  /** The shared root this binding reads and writes. */
  get root(): YNode {
    return this._root;
  }

  /** See {@link YBindingStatus}; `onStatus` reports changes. */
  get status(): YBindingStatus {
    return this._status;
  }

  /** Storage kinds the document records per node type (see the README). */
  get pins(): ReadonlyMap<
    string,
    {readonly kind: StorageKind; readonly by?: readonly string[]}
  > {
    return this._pins;
  }

  /** The collaborative undo manager; null when undo is disabled. */
  get undoManager(): UndoManager | null {
    return this._undoManager;
  }

  constructor(editor: LexicalEditor, doc: Doc, options: YBindingOptions = {}) {
    this._editor = editor;
    this._doc = doc;
    this.options = options;
    this._root = options.root || doc.get(DEFAULT_ROOT_NAME);
    this.state = new State(editor, doc, this._root);
    this.afterTransaction = tr =>
      this.guard(() => withPins(this._pins, () => this.onAfterTransaction(tr)));
    this.beforeTransaction = tr => {
      this.pendingCursor =
        this._status !== 'pending' &&
        tr.origin !== this &&
        tr.origin !== this.initOrigin &&
        tr.origin !== this.followUpOrigin
          ? this.getCursor()
          : null;
    };
  }

  /** Start listening; read the document if it is already initialized. */
  start(): () => void {
    return this.guard(() => this.startInner());
  }

  private startInner(): () => void {
    if (this.options.clientIDRange === 'uint32') {
      this.disposers.push(constrainClientID(this._doc));
    }
    // With block ids, a line without a marker gets an id derived from the
    // document (see Reader#$materialize).
    const blockIds = getPeerDependencyFromEditor<typeof BlockIdExtension>(
      this._editor,
      '@lexical/extension/BlockId',
    );
    this.state.blockIdHolder =
      blockIds === undefined ? null : id => blockIds.output.$getBlockById(id);
    this.state.blockIds =
      blockIds === undefined
        ? null
        : node =>
            !blockIds.output.disabled.peek() &&
            blockIds.output.$isIdentifiedBlock(node);
    // With transforms, BlockIdExtension's naming update changes what remote
    // changes bring, in ways the binding does not write; what they derive
    // (the start of a list they split) can differ between clients, which
    // then show different content. Fail closed rather than diverge.
    this.unsupportedConfig =
      blockIds !== undefined && blockIds.config.repairTransforms
        ? ['BlockIdExtension.repairTransforms']
        : [];
    // Lexical records explicit node moves (read by the writer, which then
    // rewrites what moved rather than what it passed).
    const recordedMoves = this._editor._recordNodeMoves;
    this._editor._recordNodeMoves = true;
    this.disposers.push(() => {
      this._editor._recordNodeMoves = recordedMoves;
    });
    // Fail closed: not editable until the layout record has been read.
    this.wasEditable = this._editor.isEditable();
    this._editor.setEditable(false);
    // Yjs cleans up formats after a remote transaction by rescanning every
    // type that has formats (whole containers here, so O(document) per remote
    // bold). The binding writes no redundant formats itself (the writer
    // cleans its own gaps), so its containers opt out: they are marked as
    // having no formats before Yjs decides whether to clean up. The
    // document's flag and the app's other types are left alone.
    this._doc.on('beforeObserverCalls', this.beforeObserverCalls);
    this.disposers.push(() =>
      this._doc.off('beforeObserverCalls', this.beforeObserverCalls),
    );
    this._doc.on('beforeTransaction', this.beforeTransaction);
    this.disposers.push(() =>
      this._doc.off('beforeTransaction', this.beforeTransaction),
    );
    this._doc.on('afterTransaction', this.afterTransaction);
    this.disposers.push(() =>
      this._doc.off('afterTransaction', this.afterTransaction),
    );
    // Warnings found while Yjs applies a change are passed on once it has
    // been applied in full (see flushWarnings).
    this._doc.on('afterAllTransactions', this.afterAllTransactions);
    this.disposers.push(() =>
      this._doc.off('afterAllTransactions', this.afterAllTransactions),
    );
    this.disposers.push(
      this._editor.registerUpdateListener(payload =>
        this.guard(() => {
          if (!this.task.committed) {
            this.task.committed = true;
            queueMicrotask(endOfTask(this.task));
          }
          withPins(this._pins, () => this.onUpdate(payload));
          if (
            this.state.hidden !== null &&
            this._editor._compositionKey === null
          ) {
            this.pending.add('hidden');
          }
          // The binding's own updates wait until the listeners are done
          // (see runPending), also work held back while composing or behind
          // a pending update; a re-read is queued as the next update (see
          // queueReread), the author's normalization right away (see
          // queueNormalize).
          if (this.pending.size > 0) {
            this.queueReread();
            this.queueNormalize();
            this.schedulePending();
          }
        }),
      ),
    );
    // Every edit is written in the normalized form its declarations describe
    // (children, mergeAdjacent), as NodeStructureExtension enforces it.
    this.disposers.push(registerNodeStructure(this._editor));
    this.disposers.push(this.noteRegistrations());
    const canonicalize = (node: LexicalNode) =>
      withPins(this._pins, () =>
        $canonicalizeGroup(node as ElementNode, this.state.blockIds),
      );
    // An item that starts or stops holding a nested group changes the
    // numbering of its group, which Lexical does not mark dirty: marked
    // here, its group's own transforms renumber it in the same update.
    const markGroupOfItem = (node: LexicalNode) =>
      withPins(this._pins, () => {
        const parent = node.getParent();
        if (
          parent === null ||
          !$isElementNode(node) ||
          getGroupSpec(klassOf(parent)) === null
        ) {
          return;
        }
        const prevMap = this._editor.getEditorState()._nodeMap;
        const prev = prevMap.get(node.getKey());
        const isGroupNode = (n: LexicalNode | null | undefined) =>
          n !== null &&
          n !== undefined &&
          $isElementNode(n) &&
          getGroupSpec(klassOf(n)) !== null;
        const wasWrapper =
          prev !== undefined &&
          $isElementNode(prev) &&
          prev.__first !== null &&
          isGroupNode(prevMap.get(prev.__first));
        if (wasWrapper !== isGroupNode(node.getFirstChild())) {
          parent.markDirty();
        }
      });
    // Which elements Lexical's transforms ran on: an update applied with
    // skipTransforms, or a state set whole, runs none on what it changes
    // (see normalizeUntransformed).
    const noteTransformed = (node: LexicalNode) => {
      this.transformed.add(node.getKey());
      if (
        $isRootNode(node) &&
        this._status === 'active' &&
        this.commitsAtOnce()
      ) {
        $flushSyncAfterUpdate();
      }
    };
    for (const {klass} of this._editor._nodes.values()) {
      if (klass.prototype instanceof ElementNode) {
        this.disposers.push(
          this._editor.registerNodeTransform(klass, noteTransformed),
        );
      }
      const spec = getGroupSpec(klass);
      if (spec !== null && spec.klass === klass) {
        this.disposers.push(
          this._editor.registerNodeTransform(klass, canonicalize),
        );
        for (const item of spec.items) {
          this.disposers.push(
            this._editor.registerNodeTransform(item, markGroupOfItem),
          );
        }
      }
    }
    // A line break inside a text node ("a\nb", from code) is stored, and
    // read by every client, as a line break node: the author's text node is
    // split the same way in its own edit, so its editor shows the document.
    // Every text node class (token and segmented text, a code highlight).
    for (const {klass} of this._editor._nodes.values()) {
      if (klass === TextNode || klass.prototype instanceof TextNode) {
        this.disposers.push(
          this._editor.registerNodeTransform(
            klass as Klass<TextNode>,
            $splitLineBreaks,
          ),
        );
      }
    }
    if (this.options.captureTimeout !== null) {
      const um = new UndoManager(this._root, {
        captureTimeout: this.options.captureTimeout ?? 500,
        deleteFilter: item => !this.isKeptByUndo(item),
        trackedOrigins: new Set([this]),
      });
      this._undoManager = um;
      // Each step keeps the selection from before it, which undoing it
      // restores (as @lexical/history does): a local edit's from before the
      // edit, and the step an undo or redo pushes to the other stack the
      // selection from when it was undone or redone.
      um.on('stack-item-added', ({stackItem, origin}) => {
        stackItem.meta.set(
          this,
          origin === um ? this.undoneCursor : this.writeCursor,
        );
      });
      this.disposers.push(() => um.destroy());
    }
    this.noteTransforms();
    this.evaluate();
    return () => this.dispose();
  }

  /** Disconnect from the document and the editor (`start` returns this). */
  dispose(): void {
    for (const d of this.disposers.splice(0)) {
      d();
    }
    // A pending or read-only binding made the editor non-editable: give it
    // back as it was before the binding.
    if (this._status !== 'active') {
      this._editor.setEditable(this.wasEditable);
    }
    this.state.clear();
    this.pending.clear();
    this.localRefresh.clear();
    this.refused.clear();
    this.toSettle.clear();
    this.untransformed.clear();
    this.untransformedText.clear();
    this.registrationPasses.length = 0;
    this._undoManager = null;
    this.flushWarnings();
  }

  /**
   * Call after the provider's first sync. An empty root is marked with this
   * layout and gets the editor's current content, unless an older layout's
   * root (`root`, `root-v2`) has content: such a document is read only, and
   * must be converted instead (a binding with `convert: true` writes the
   * layout root next to the old one). Anything else is read.
   *
   * The initial content (including an update still pending, such as
   * `editor.update(seed)` right before this call) is not part of the undo
   * history. Into a pristine top-level root (one that has never held an
   * item or an attribute), it is written once, under a client id derived
   * from those exact bytes (see seedUpdate), applied to the document as they
   * are and read back like any document, so that two clients initializing
   * the same document with the same content at once write the same items
   * (one copy), and one id never holds two payloads; anywhere else, with
   * this client's own id.
   */
  initialize(): void {
    this.guard(() => withPins(this._pins, () => this.initializeInner()));
  }

  private initializeInner(): void {
    if (this._status !== 'pending') {
      return;
    }
    if (this._root.length === 0 && recordedLayout(this._root) === null) {
      const legacy = this.options.convert ? [] : this.legacyRootsWithContent();
      if (legacy.length > 0) {
        this.warn(
          UNSUPPORTED_LAYOUT_WARNING,
          `@lexical/y: the document has content in ${legacy.join(', ')} (an older layout); convert it to this layout instead of initializing it.`,
          {layout: undefined, legacyRoots: legacy},
        );
        this.setStatus('readonly');
        return;
      }
      if (this.unsupportedConfig.length > 0) {
        // Read only (see setStatus): the initial content is not written.
        this.setStatus('active');
        return;
      }
      // An update still pending (`editor.update(seed)` right before this
      // call) is part of the initial content: committed now, while the
      // binding is pending and writes nothing, then written with it.
      this.commitPending();
      const editorState = this._editor.getEditorState();
      if (this.refuseUnstorableSlots(editorState, null)) {
        return;
      }
      // Not pristine (it held an item or an attribute, deleted since): under
      // a derived id, two clients' copies could differ in what they write
      // around those, so it is written under this client's own id; so is a
      // root inside another shared type (see seedUpdate).
      const seed =
        this._root._start !== null || this._root._map.size > 0
          ? null
          : this.seedUpdate(editorState);
      // What the cursor leaves out of the selection (a range's typing format
      // and style, a node selection), kept too.
      const kept = editorState.read($selectionState);
      if (seed !== null) {
        // The seed's exact bytes, under the id derived from them, the
        // binding's only items under another client id than the document's;
        // read back like any document's content, so the editor shows what
        // is stored (and the state maps it), with its selection kept.
        applyUpdate(this._doc, seed.bytes, this.initOrigin);
        this.evaluate(seed.cursor, kept);
        return;
      }
      this._doc.transact(tr => {
        this.$writeInitial(this.state, this._root, tr, editorState);
      }, this.initOrigin);
      // Read back as the seed is, so that the editor shows what is stored on
      // every route (text written with a line break in it shows as a line
      // break node, as on every reader), with its selection kept.
      this.evaluate(
        editorState.read(() => this.$cursorBeforeRead()),
        kept,
      );
      return;
    }
    this.evaluate();
  }

  /**
   * Write the layout record and the editor's content into an empty root, the
   * record first (see LAYOUT_PREFIX).
   */
  private $writeInitial(
    state: State,
    root: YNode,
    tr: Transaction,
    editorState: EditorState,
  ): void {
    root.setAttr(LAYOUT_PREFIX + LAYOUT_VERSION, true);
    // Every element type of the initial content (into `root`, which may be
    // a scratch document's: this._pins is filled when the real one is read).
    this.recordPins(root, editorState, null, new Map());
    editorState.read(() => {
      const roles = new Roles(state);
      const cs = state.newCS(root, 'root', 'b');
      const writer = new Writer(state, roles, tr, editorState, {
        attrs: new Set(),
        inline: new Set(),
        lines: new Set(),
        removedText: new Map(),
        structural: new Set(['root']),
      });
      writer.$writeContainer(cs, $getRoot());
    });
  }

  private clientIDRange(): ClientIDRange {
    return this.options.clientIDRange === 'uint32' ? 'uint32' : 'uint53';
  }

  /**
   * The initial content of a pristine top-level root as a Yjs update,
   * written once: into a scratch document under a fixed client id, with this
   * binding's configuration (with or without block ids, and which blocks are
   * identified, change the items), hashed with the layout version and the
   * root's name into a client id, and written again under that id the same
   * way (the writer gives the same items for the same input). So two clients
   * share an id only when they write the same bytes into the same root. It
   * is the scratch state's first write, so its segment keys are that id and
   * a counter from 0 on every client. Null for a root inside another shared
   * type: its update would name that type's item, which a scratch document
   * does not hold.
   */
  private seedUpdate(
    editorState: EditorState,
  ): {bytes: Uint8Array; cursor: YCursor | null} | null {
    if (this._root._item !== null) {
      return null;
    }
    let name: string | null = null;
    this._doc.share.forEach((type, key) => {
      if (type === this._root) {
        name = key;
      }
    });
    if (name === null) {
      return null;
    }
    const rootName: string = name;
    const write = (clientID: number) => {
      const scratch = new Doc({gc: false});
      scratch.clientID = clientID;
      const sroot = scratch.get(rootName);
      const sstate = this.state.configuredLike(scratch, sroot);
      scratch.transact(tr =>
        this.$writeInitial(sstate, sroot, tr, editorState),
      );
      // The editor's selection, as positions on the items written: the
      // same ids in the document once the bytes are applied.
      const cursor = editorState.read(() => this.$cursorBeforeRead(sstate));
      const bytes = encodeStateAsUpdate(scratch);
      scratch.destroy();
      return {bytes, cursor};
    };
    const {bytes} = write(1);
    let content = '';
    for (let i = 0; i < bytes.length; i += 4096) {
      content += String.fromCharCode.apply(
        null,
        Array.from(bytes.subarray(i, i + 4096)),
      );
    }
    return write(
      initClientID(
        LAYOUT_VERSION + '\u0000' + 'r:' + rootName + '\u0000' + content,
        this.clientIDRange(),
      ),
    );
  }

  /** Older layouts' roots that hold content. */
  private legacyRootsWithContent(): string[] {
    const out: string[] = [];
    for (const name of LEGACY_ROOTS) {
      const type = this._doc.share.get(name);
      if (type === undefined) {
        continue;
      }
      let content = type._map.size > 0;
      for (let it = type._start; it !== null && !content; it = it.right) {
        if (!it.deleted) {
          content = true;
        }
      }
      if (content) {
        out.push(name);
      }
    }
    return out;
  }

  /**
   * Read the kinds the document records per type. A registered class whose
   * own derivation differs uses the recorded kind when it can be stored that
   * way; otherwise the document is read only (returns false).
   */
  private loadPins(): boolean {
    this._pins.clear();
    const attrs = this._root.getAttrs() as Record<string, unknown>;
    const conflicts: string[] = [];
    const conflicting: string[] = [];
    for (const key of Object.keys(attrs)) {
      const v = attrs[key];
      if (key.startsWith(PIN_PREFIX) && typeof v !== 'string') {
        // Not a record this editor can read: writing would overwrite it.
        const type = key.slice(PIN_PREFIX.length);
        conflicting.push(type);
        conflicts.push(`${type} (document: ${JSON.stringify(v)})`);
      } else if (key.startsWith(PIN_PREFIX) && typeof v === 'string') {
        // `kind` or `kind|field,field` (a group's or format's identity).
        const [kind, by] = v.split('|');
        this._pins.set(key.slice(PIN_PREFIX.length), {
          by: by === undefined ? undefined : by.split(','),
          kind: kind as Pin['kind'],
        });
      }
    }
    for (const [type, pin] of this._pins) {
      const info = this._editor._nodes.get(type);
      if (info === undefined) {
        continue;
      }
      const derived = deriveStorageKind(info.klass);
      const by = identityOf(info.klass);
      if (pin.kind !== derived && !canStoreAs(info.klass, pin.kind)) {
        conflicting.push(type);
        conflicts.push(
          `${type} (document: ${pin.kind}, this editor: ${derived})`,
        );
      } else if (
        (pin.kind === 'group' || pin.kind === 'format') &&
        pin.by !== undefined &&
        pin.kind === derived &&
        JSON.stringify(pin.by) !== JSON.stringify(by)
      ) {
        conflicting.push(type);
        conflicts.push(
          `${type} (document identity: ${pin.by.join(',')}, this editor: ${by.join(',')})`,
        );
      }
    }
    if (conflicts.length > 0) {
      this.warn(
        STORAGE_MISMATCH_WARNING,
        `@lexical/y: the document stores node types in a way this editor cannot (${conflicts.join('; ')}); it is read only.`,
        {types: conflicting},
      );
      this.setStatus('readonly');
      return false;
    }
    return true;
  }

  /** Record the kind of every element type written for the first time. */
  private recordPins(
    root: YNode,
    editorState: EditorState,
    keys: readonly NodeKey[] | null,
    pins: Map<string, Pin> = this._pins,
  ): void {
    const nodeMap = editorState._nodeMap;
    const seen = new Set<string>();
    const visit = (node: LexicalNode | undefined) => {
      if (node === undefined || !$isElementNode(node) || $isRootNode(node)) {
        return;
      }
      const type = node.getType();
      if (seen.has(type) || pins.has(type)) {
        return;
      }
      seen.add(type);
      const klass = node.constructor as Klass<LexicalNode>;
      const kind = storageKindOf(klass);
      const pin: Pin =
        kind === 'group' || kind === 'format'
          ? {by: identityOf(klass), kind}
          : {kind};
      pins.set(type, pin);
      root.setAttr(
        PIN_PREFIX + type,
        pin.by === undefined ? kind : kind + '|' + pin.by.join(','),
      );
    };
    withPins(this._pins, () => {
      if (keys === null) {
        for (const node of nodeMap.values()) {
          visit(node);
        }
      } else {
        for (const key of keys) {
          visit(nodeMap.get(key));
        }
      }
    });
  }

  /**
   * Read the document's layout and content (`cursor` and `kept`: the
   * selection to put back on it, see initializeInner; otherwise there is
   * none).
   */
  private evaluate(
    cursor: YCursor | null = null,
    kept: SelectionState | null = null,
  ): void {
    if (!this.loadPins()) {
      this.readAll(cursor, kept);
      return;
    }
    const version = recordedLayout(this._root);
    if (version === null) {
      if (this._root.length > 0 || this._status === 'active') {
        // Content without a layout record, or a record removed from a
        // document this binding was writing (an outside writer deleted it;
        // no client of this layout deletes one): no layout is known, so
        // nothing is written.
        this.warn(
          UNSUPPORTED_LAYOUT_WARNING,
          this._root.length > 0
            ? '@lexical/y: the shared root has content but no layout version; it is read only.'
            : '@lexical/y: the layout record of the document was removed; it is read only.',
          {layout: undefined, legacyRoots: []},
        );
        this.setStatus('readonly');
        this.readAll(cursor, kept);
      }
      return;
    }
    if (Number.isNaN(version) || version > LAYOUT_VERSION) {
      this.warn(
        UNSUPPORTED_LAYOUT_WARNING,
        Number.isNaN(version)
          ? '@lexical/y: the layout record of the document is not one this version reads; it is read only.'
          : `@lexical/y: the document uses layout ${version}, not one this version supports (1 to ${LAYOUT_VERSION}); it is read only.`,
        {layout: Number.isNaN(version) ? undefined : version, legacyRoots: []},
      );
      this.setStatus('readonly');
    } else {
      this.setStatus('active');
    }
    this.readAll(cursor, kept);
  }

  /** Self-check of containers a remote change rebuilt (see checkContainer). */
  private checkRead(rebuilt: ReadonlySet<CS>): void {
    const check = this.options.selfCheck === true;
    // Not while the editor shows a follow-up's change the binding did not
    // write (an update that followed the read, such as the one naming its
    // blocks): it is read again right after (see rereadRefused).
    if (
      !check ||
      rebuilt.size === 0 ||
      this.refused.size > 0 ||
      Math.random() >= (this.options.selfCheckSample ?? 1)
    ) {
      return;
    }
    const editorState = this._editor.getEditorState();
    const problems: string[] = [];
    const wrong: CS[] = [];
    for (const cs of rebuilt) {
      if (sampleWholeContainer(cs)) {
        const found = checkContainer(this.state, cs, editorState);
        if (found.length > 0) {
          wrong.push(cs);
          // A line holding lines (written without the normalization, which
          // has not run yet) is stored as the lines the normalization leaves
          // (see Writer#$pushLine): the editor differs from the shared
          // content there until it runs. The read below brings it in line,
          // which is no reader bug.
          if (!editorState.read(() => this.$holdsWrittenLines(cs))) {
            pushAll(problems, found);
          }
        }
      }
    }
    if (problems.length > 0) {
      this.warn(
        SELF_CHECK_WARNING,
        '@lexical/y self-check (remote): ' + problems.slice(0, 5).join('; '),
        {problems, remote: true},
      );
    }
    if (wrong.length > 0) {
      // After a remote change the shared content is right and the editor is
      // wrong (a reader bug): read those containers again in full, which
      // moves this client to what every fresh reader shows.
      this.rereadContainers(wrong);
    }
  }

  /**
   * Whether the editor's element of container `cs` holds, at any depth (the
   * comparison covers the containers inside it), a line that holds lines
   * (see Writer#$pushLine).
   */
  private $holdsWrittenLines(cs: CS): boolean {
    const el = cs.y === this._root ? $getRoot() : $getNodeByKey(cs.key);
    if (!$isElementNode(el) || !el.isAttached()) {
      return false;
    }
    const roles = new Roles(this.state);
    const visit = (n: ElementNode): boolean => {
      for (const c of n.getChildren()) {
        if (!$isElementNode(c)) {
          continue;
        }
        if (roles.$role(c) === 'line') {
          if ($holdsLines(roles, c)) {
            return true;
          }
        } else if (visit(c)) {
          return true;
        }
      }
      return false;
    };
    return visit(el);
  }

  private rereadContainers(list: CS[], extraTags: string[] = []): void {
    this.commitPending();
    let error: unknown = null;
    this._editor.update(
      () => {
        try {
          const cursor = this.$cursorBeforeRead();
          const reader = new Reader(this.state);
          for (const cs of list) {
            const el = cs.y === this._root ? $getRoot() : $getNodeByKey(cs.key);
            if ($isElementNode(el) && el.isAttached()) {
              reader.$readFull(cs, el);
            }
          }
          this.$selectionAfterRead(cursor);
          this.$quietSelection();
        } catch (e) {
          error = e;
        }
      },
      {
        discrete: true,
        skipTransforms: true,
        tag: [...REMOTE_TAGS, ...extraTags],
      },
    );
    if (error !== null) {
      this.recoverRead(error);
    }
  }

  /**
   * Fail closed on named slots the document cannot store (see
   * $unstorableSlotHosts), among the nodes `keys` of `editorState` (all of
   * them when null): warn and open read only, without writing. Returns
   * whether it did.
   */
  private refuseUnstorableSlots(
    editorState: EditorState,
    keys: Iterable<NodeKey> | null,
  ): boolean {
    const types = editorState.read(() =>
      $unstorableSlotHosts(new Roles(this.state), keys, editorState._nodeMap),
    );
    if (types.length === 0) {
      return false;
    }
    this.warn(
      UNSUPPORTED_SLOTS_WARNING,
      `@lexical/y: ${types.join(', ')} nodes hold named slots where the document cannot store them (on a node stored as a line, a format or a group, or on the root); the change is not written and the document is read only.`,
      {types},
    );
    this.setStatus('readonly');
    return true;
  }

  /** Fail closed when a read found node types this editor lacks. */
  private checkUnknownTypes(): void {
    const unknown = this.state.unknownTypes;
    if (unknown.size > 0 && this._status === 'active') {
      const types = [...unknown].sort();
      this.warn(
        UNKNOWN_NODE_TYPES_WARNING,
        `@lexical/y: the document has node types this editor does not register (${types.join(
          ', ',
        )}); it is read only, so that content is not hidden and then deleted.`,
        {types},
      );
      this.setStatus('readonly');
    }
  }

  private setStatus(status: YBindingStatus): void {
    if (status === 'active' && this.unsupportedConfig.length > 0) {
      const options = this.unsupportedConfig;
      if (this._status !== 'readonly') {
        this.warn(
          UNSUPPORTED_CONFIG_WARNING,
          `@lexical/y: the editor is configured in a way the binding cannot write safely (${options.join(
            ', ',
          )}: set repairTransforms: false); it is read only.`,
          {options},
        );
      }
      status = 'readonly';
    }
    if (this._status !== status && this.options.onStatus) {
      // Reported with the warnings, once Yjs is idle (see flushWarnings).
      this.pendingStatus = status;
    }
    this._status = status;
    this._editor.setEditable(status === 'active' && this.wasEditable);
    // Nothing is written while read only, an undo or redo included: the
    // undo history goes, which a direct UndoManager call could still apply.
    if (status === 'readonly' && this._undoManager !== null) {
      this._undoManager.clear();
    }
  }

  /**
   * Report a warning to the editor's `onWarn`, as a `LexicalWarning`. It is
   * queued and passed on once the binding's work is done and Yjs is idle:
   * never inside a Yjs observer or transaction, and never half way through
   * a read or a write (see flushWarnings).
   */
  private warn(code: YWarningCode, message: string, data: unknown): void {
    this.pendingWarnings.push(new LexicalWarning(code, message, data));
  }

  /** Run the binding's own work; queued warnings are passed on after it. */
  private guard<T>(fn: () => T): T {
    this.busy++;
    try {
      return fn();
    } finally {
      this.busy--;
      this.flushWarnings();
    }
  }

  /**
   * Pass the queued warnings to the editor's `onWarn`, when nothing is in
   * progress: no work of the binding's (see guard) and no Yjs transaction
   * (the change has been applied, observers included; afterAllTransactions
   * calls this again). A handler that throws does not stop the others or
   * the binding, which is consistent by then: its error is rethrown in a
   * microtask (an uncaught error, as Lexical's default `onWarn` throws in
   * development), never into Yjs or a provider.
   */
  private flushWarnings(): void {
    // Warnings about classes and values (see noteOnce), found by any
    // binding: each binding reports each once, a class's only where its
    // editor has the class.
    const [notes, seen] = notesSince(this.notesSeen);
    this.notesSeen = seen;
    for (const note of notes) {
      const data = note.data as {type?: unknown} | null;
      const type = data === null ? undefined : data.type;
      if (typeof type !== 'string' || this._editor._nodes.has(type)) {
        this.warn(note.code, note.message, note.data);
      }
    }
    const doc = this._doc;
    if (
      this.flushingWarnings ||
      this.busy > 0 ||
      (this.pendingWarnings.length === 0 && this.pendingStatus === null) ||
      doc._transaction !== null ||
      doc._transactionCleanups.length > 0
    ) {
      return;
    }
    this.flushingWarnings = true;
    try {
      const status = this.pendingStatus;
      this.pendingStatus = null;
      if (status !== null && this.options.onStatus) {
        try {
          this.options.onStatus(status);
        } catch (error) {
          queueMicrotask(() => {
            throw error;
          });
        }
      }
      for (
        let warning = this.pendingWarnings.shift();
        warning !== undefined;
        warning = this.pendingWarnings.shift()
      ) {
        try {
          this._editor._onWarn(warning);
        } catch (error) {
          queueMicrotask(() => {
            throw error;
          });
        }
      }
    } finally {
      this.flushingWarnings = false;
    }
  }

  private readAll(
    cursor: YCursor | null = null,
    kept: SelectionState | null = null,
  ): void {
    this._editor.update(
      () => {
        const reader = new Reader(this.state);
        let cs = this.state.containers.get(this._root);
        if (cs === undefined) {
          cs = this.state.newCS(this._root, 'root', 'b');
        }
        reader.$readFull(cs, $getRoot());
        $setSelection(null);
        if (cursor !== null) {
          this.$restoreSelection(cursor);
        }
        if (kept !== null) {
          $restoreSelectionState(kept);
        }
        this.$quietSelection();
      },
      {
        discrete: true,
        skipTransforms: true,
        tag: REMOTE_TAGS,
      },
    );
    this.checkUnknownTypes();
    this.flushRefresh(true);
  }

  // -------------------------------------------------------------------------
  // Remote -> Lexical

  private onAfterTransaction(tr: Transaction): void {
    if (
      tr.origin === this ||
      tr.origin === this.initOrigin ||
      tr.origin === this.followUpOrigin ||
      tr.origin === this.scanOrigin
    ) {
      return;
    }
    this.remoteSeq++;
    if (this._status === 'pending') {
      if (recordedLayout(this._root) !== null) {
        this.evaluate();
      }
      return;
    }
    const state = this.state;
    const childItems = new Map<YNode, Item[]>();
    const add = (s: unknown) => {
      if (
        s instanceof Item &&
        s.parentSub === null &&
        s.parent instanceof YNode
      ) {
        if (!state.containers.has(s.parent)) {
          return;
        }
        let list = childItems.get(s.parent);
        if (list === undefined) {
          list = [];
          childItems.set(s.parent, list);
        }
        list.push(s);
      }
    };
    iterateStructsByIdSet(tr, tr.insertSet, add);
    iterateStructsByIdSet(tr, tr.deleteSet, add);
    const attrKeys = new Map<YNode, Set<string>>();
    tr.changed.forEach((subs, type) => {
      const keys = new Set<string>();
      subs.forEach(k => {
        if (k !== null) {
          keys.add(k);
        }
      });
      if (keys.size === 0) {
        return;
      }
      if (type === this._root) {
        if ([...keys].some(k => k.startsWith(LAYOUT_PREFIX))) {
          this.evaluate();
        } else if ([...keys].some(k => k.startsWith(PIN_PREFIX))) {
          this.loadPins();
        }
        return;
      }
      const isOurs =
        state.keyByY.has(type) ||
        (type.name === MARKER &&
          type._item !== null &&
          state.unitByEnd.has(type._item));
      if (isOurs) {
        attrKeys.set(type, keys);
      }
    });
    if (childItems.size === 0 && attrKeys.size === 0) {
      // Nothing to read: the binding's own updates waiting for the editor
      // can run now (see runPending).
      this.runPending();
      return;
    }
    // A local update still pending (an editor.update() in the same task,
    // e.g. from an app's observer of another shared type) is committed and
    // written first: the remote read must not absorb it untagged-as-local.
    this.commitPending();
    let cursor = this.pendingCursor;
    this.pendingCursor = null;
    // An undo puts back the selection of its step (a range, after typing
    // over one); any other read keeps the user's caret a caret.
    const undoing =
      tr.origin === this._undoManager && this._undoManager !== null;
    if (undoing) {
      this.undoneCursor = cursor;
      cursor = this.stepCursor ?? cursor;
    }
    const changedKeys: NodeKey[] = [];
    let rebuilt: ReadonlySet<CS> = new Set();
    let readError: unknown = null;
    // A re-read of a naming update's change is tagged as that update (see
    // rereadRefused).
    const naming = this.refused.size > 0 && this.refusedNaming;
    const after = () => {
      if (readError !== null) {
        this.recoverRead(readError);
        return;
      }
      this.checkUnknownTypes();
      this.checkRead(rebuilt);
      this.flushRefresh(true);
      // The binding's own updates waiting for the editor (a follow-up of the
      // read whose change was not written is read again): now that the
      // editor shows the change, never before (a write then would take what
      // the editor does not show yet for deleted).
      this.runPending();
    };
    // Applied while the editor is updating (an undo the binding runs in an
    // update of its own, see undo): the read is part of that update, and
    // what follows it waits for its commit.
    const nested = this._editor._updating;
    this._editor.update(
      () => {
        try {
          this.$readRemote(
            state,
            childItems,
            attrKeys,
            cursor,
            !undoing,
            changedKeys,
            r => {
              rebuilt = r;
            },
          );
        } catch (e) {
          readError = e;
        }
        if (nested) {
          $onUpdate(() => this.guard(() => withPins(this._pins, after)));
        }
      },
      {
        discrete: true,
        skipTransforms: true,
        tag: naming ? [...REMOTE_TAGS, BLOCK_ID_REPAIR_TAG] : REMOTE_TAGS,
      },
    );
    if (!nested) {
      after();
    }
  }

  private $readRemote(
    state: State,
    childItems: Map<YNode, Item[]>,
    attrKeys: Map<YNode, Set<string>>,
    cursor: YCursor | null,
    keepCaret: boolean,
    changedKeys: NodeKey[],
    setRebuilt: (rebuilt: ReadonlySet<CS>) => void,
  ): void {
    const reader = new Reader(state);
    setRebuilt(reader.rebuilt);
    const composing = this.$composingOwner();
    reader.composingKey = composing;
    // A container that still shows a follow-up's change the binding did not
    // write is read in full first: the reader changes only what the
    // transaction touched, on an editor it takes to show the document.
    for (const cs of this.refused) {
      const el = cs.y === this._root ? $getRoot() : $getNodeByKey(cs.key);
      if (
        state.containers.get(cs.y) === cs &&
        $isElementNode(el) &&
        el.isAttached()
      ) {
        reader.$readFull(cs, el);
      }
    }
    this.refused.clear();
    this.refusedNaming = false;
    for (const id of this.toSettle) {
      state.touchedIds.add(id);
    }
    this.toSettle.clear();
    reader.$apply(childItems, attrKeys);
    // Remote inserts into the line being composed are shown when the
    // composition ends (see Hidden).
    let hidden = state.hidden;
    if (hidden !== null && hidden.ownerKey !== composing) {
      // The composition it was held back for has ended (another may have
      // started since, its own update waiting for the editor to be idle):
      // what it held back shows now.
      state.hidden = null;
      if (!reader.$refreshComposed(hidden.ownerKey)) {
        // The composed line is gone (a local edit removed or moved it):
        // what was hidden in it is read where it is now (see flushHidden).
        new Reader(state).$apply(this.hiddenItems(hidden), new Map());
      }
      hidden = null;
    } else if (hidden !== null && reader.composingRead) {
      // The composed line was read in full: everything in it shows.
      hidden = null;
    }
    if (!reader.composingRead && reader.deferred.length > 0) {
      if (hidden === null) {
        hidden = new Hidden(composing!);
      }
      for (const it of reader.deferred) {
        hidden.add(it.id.client, it.id.clock, it.length);
      }
    }
    state.hidden = hidden;
    if (cursor !== null) {
      this.$restoreSelection(cursor, keepCaret);
    }
    $clampSelection();
    this.$caretOnText();
    this.$quietSelection();
    for (const y of childItems.keys()) {
      const key = state.keyByY.get(y);
      if (key !== undefined) {
        changedKeys.push(key);
      }
    }
  }

  /**
   * A remote read that throws (a reader bug) must not leave this client
   * showing something else than the document for good: the editor is
   * rebuilt from the shared content (a fresh reader's result, which every
   * client converges on) in a fresh update, and the failure is reported.
   */
  private recoverRead(error: unknown): void {
    this.warn(
      RECOVERED_READ_WARNING,
      `@lexical/y: a remote change could not be read and the editor was rebuilt from the document: ${String(
        error instanceof Error ? error.message : error,
      )}`,
      {error},
    );
    try {
      this.rebuildFromDocument();
    } catch (e) {
      this._editor._onError(e instanceof Error ? e : new Error(String(e)));
    }
  }

  /**
   * Inside an update: replace the editor's content with a fresh read of the
   * shared root, on a new state.
   */
  private $rebuild(): void {
    // With what startInner configured on the state it replaces.
    this.state = this.state.configuredLike(this._doc, this._root);
    const root = $getRoot();
    root.clear();
    const reader = new Reader(this.state);
    const cs = this.state.newCS(this._root, 'root', 'b');
    reader.$readFull(cs, root);
    $setSelection(null);
    this.$quietSelection();
  }

  /** Replace the editor's content with a fresh read of the shared root. */
  private rebuildFromDocument(): void {
    this.commitPending();
    let error: unknown = null;
    this._editor.update(
      () => {
        try {
          this.$rebuild();
        } catch (e) {
          error = e;
        }
      },
      {
        discrete: true,
        skipTransforms: true,
        tag: REMOTE_TAGS,
      },
    );
    if (error !== null) {
      throw error;
    }
    this.checkUnknownTypes();
    this.flushRefresh(true);
  }

  /**
   * The line or inline container holding the node being composed (IME), if
   * the binding stores it as one.
   */
  private $composingOwner(): NodeKey | null {
    const key = this._editor._compositionKey;
    const node = key === null ? null : $getNodeByKey(key);
    if (node === null || !node.isAttached()) {
      return null;
    }
    const owner = $isTextNode(node) ? $ownerOf(node) : null;
    if (owner === null) {
      return null;
    }
    const ownerKey = owner.getKey();
    const unit = this.state.unitByKey.get(ownerKey);
    if (unit !== undefined && unit.kind === 'line') {
      return ownerKey;
    }
    const cs = this.state.csByKey.get(ownerKey);
    return cs !== undefined && cs.kind === 'i' ? ownerKey : null;
  }

  /** Show the remote content hidden during a composition that has ended. */
  private flushHidden(): void {
    const hidden = this.state.hidden;
    if (hidden === null) {
      return;
    }
    const cursor = this.getCursor();
    this.state.hidden = null;
    this._editor.update(
      () => {
        const reader = new Reader(this.state);
        if (!reader.$refreshComposed(hidden.ownerKey)) {
          // A local edit removed the composed line: what was hidden in it is
          // read where it is now (a line of its own, or joined into another).
          reader.$apply(this.hiddenItems(hidden), new Map());
        }
        if (cursor !== null) {
          this.$restoreSelection(cursor, true);
        }
        this.$caretOnText();
        this.$quietSelection();
      },
      {
        discrete: true,
        skipTransforms: true,
        tag: REMOTE_TAGS,
      },
    );
  }

  /** The items of the binding's containers that `hidden` holds. */
  private hiddenItems(hidden: Hidden): Map<YNode, Item[]> {
    const out = new Map<YNode, Item[]>();
    hidden.forEachRange((client, start, end) => {
      const structs = this._doc.store.clients.get(client);
      if (structs === undefined) {
        return;
      }
      for (
        let i = findIndexSS(structs, start);
        i < structs.length && structs[i].id.clock < end;
        i++
      ) {
        const s = structs[i];
        if (
          s instanceof Item &&
          s.parent instanceof YNode &&
          this.state.containers.has(s.parent)
        ) {
          let list = out.get(s.parent);
          if (list === undefined) {
            list = [];
            out.set(s.parent, list);
          }
          list.push(s);
        }
      }
    });
    return out;
  }

  /**
   * Recompute the derived fields (list numbering) of the groups a read or a
   * change touched. The group class's own transforms run directly, with the
   * group's siblings hidden: a transform that would also restructure (merge
   * an adjacent equal list) must not, as each peer would write that merge
   * (duplicating its items) and a fresh reader would build another tree.
   *
   * After a remote change (`remote`) in an editor that is not focused, the
   * refresh does not set the DOM selection (SKIP_DOM_SELECTION_TAG): the read
   * already restored it, and setting it would move the focus into that
   * editor. A focused editor sets it as usual, so a refresh that reshapes the
   * DOM under the caret (an app's list transform) keeps the caret in place.
   */
  private flushRefresh(
    remote: boolean,
    from: Set<NodeKey> = this.state.refresh,
  ): void {
    if (from.size === 0) {
      return;
    }
    if (this._editor._updating && this._editor._pendingEditorState === null) {
      // In a listener phase, or right after a commit (a read the binding
      // ran as an update of its own, such as an undo's): the refresh is the
      // next update, on its own (see queueFirst).
      const keys = [...from];
      from.clear();
      this.queueFirst(
        () => {
          for (const tag of this.refreshTags(remote)) {
            $addUpdateTag(tag);
          }
          this.$refreshGroups(keys);
        },
        {discrete: true, skipTransforms: true},
      );
      return;
    }
    if (!this.isIdle()) {
      // Inside another update (a change applied from one of its listeners):
      // the refresh must commit on its own (see runPending).
      const to = remote ? this.remoteRefresh : this.localRefresh;
      if (to !== from) {
        for (const key of from) {
          to.add(key);
        }
        from.clear();
      }
      this.pending.add('refresh');
      this.schedulePending();
      return;
    }
    const keys = [...from];
    from.clear();
    this._editor.update(() => this.$refreshGroups(keys), {
      discrete: true,
      skipTransforms: true,
      tag: this.refreshTags(remote),
    });
  }

  /**
   * The refresh is no one's edit (only users' own edits write): tagged
   * COLLABORATION_TAG too, as every other update the binding makes (its
   * reads), so that an app's listener that skips that tag skips it.
   */
  private refreshTags(remote: boolean): string[] {
    return remote && !this.hasFocus()
      ? [
          COLLABORATION_TAG,
          HISTORY_MERGE_TAG,
          REFRESH_TAG,
          SKIP_DOM_SELECTION_TAG,
        ]
      : [COLLABORATION_TAG, HISTORY_MERGE_TAG, REFRESH_TAG];
  }

  /**
   * The refresh itself, inside an update (see flushRefresh). It runs the
   * group class's own transforms (list numbering) and those registered for
   * every node type, not those an app registers for lists (an app's list
   * policy applies to its users' own edits), and
   * nothing it changes is written (only users' own edits write): the class's
   * transforms derive the same fields from the same document on every
   * client and in every fresh reader, and a later local edit that writes
   * those lines writes them as the editor shows them (a structural write
   * rewrites every marker whose group fields differ from the editor's). A
   * class transform that changes a group's structure there is read again
   * (see rereadRefused).
   */
  private $refreshGroups(keys: NodeKey[]): void {
    const roles = new Roles(this.state);
    // Transforms registered for every node type (the node structure
    // normalization's collection of what to check next, BlockIdExtension's):
    // those on paragraphs.
    const paragraph = this._editor._nodes.get('paragraph');
    const everyType =
      paragraph === undefined ? undefined : paragraph.transforms;
    for (const key of keys) {
      const node = $getNodeByKey(key);
      if (!$isElementNode(node) || !node.isAttached()) {
        continue;
      }
      const info = this._editor._nodes.get(node.getType());
      if (info === undefined) {
        continue;
      }
      let own = this.classTransforms.get(info.klass);
      if (own === undefined) {
        own = getTransformSetFromKlass(info.klass);
        this.classTransforms.set(info.klass, own);
      }
      const transforms = [...info.transforms].filter(
        t => own.has(t) || (everyType !== undefined && everyType.has(t)),
      );
      const writable = node.getWritable();
      const {__prev, __next} = writable;
      const shape = $shapeOf(writable);
      writable.__prev = null;
      writable.__next = null;
      try {
        for (const transform of transforms) {
          if (writable.isAttached()) {
            transform(writable);
          }
        }
      } finally {
        writable.__prev = __prev;
        writable.__next = __next;
      }
      if (!writable.isAttached() || $shapeOf(writable) !== shape) {
        const container = writable.isAttached()
          ? roles.$containerOf(writable)
          : null;
        const cs =
          container === null || $isRootNode(container)
            ? this.state.containers.get(this._root)
            : this.state.csByKey.get(container.getKey());
        if (cs !== undefined) {
          this.refused.add(cs);
          this.pending.add('reread');
        }
      }
    }
  }

  /** Whether the focus is inside this editor's root element. */
  private hasFocus(): boolean {
    const root = this._editor.getRootElement();
    return root !== null && root.contains(getActiveElement(root));
  }

  // -------------------------------------------------------------------------
  // Lexical -> Yjs

  private onUpdate(payload: {
    dirtyElements: Map<NodeKey, boolean>;
    dirtyLeaves: Set<NodeKey>;
    editorState: EditorState;
    prevEditorState: EditorState;
    tags: Set<string>;
  }): void {
    const {editorState, prevEditorState, tags} = payload;
    let {dirtyElements, dirtyLeaves} = payload;
    // What Lexical's transforms ran on in this commit (see
    // normalizeUntransformed).
    const transformed = new Set(this.transformed);
    this.transformed.clear();
    const refresh = tags.has(REFRESH_TAG);
    // A remote change read (the refresh is tagged so too, see refreshTags).
    const remote = tags.has(COLLABORATION_TAG) && !refresh;
    // The groups this commit's refresh recomputes (see flushRefresh): not
    // those whose own transforms ran in it.
    const localKeys = new Set<NodeKey>();
    if (
      !refresh &&
      !tags.has(SKIP_COLLAB_TAG) &&
      !remote &&
      // BlockIdExtension's naming only sets block ids.
      !tags.has(BLOCK_ID_REPAIR_TAG)
    ) {
      // Every group whose children (or whose items' children) changed
      // recomputes its derived fields (list item values) in a refresh, unless
      // its own transforms ran in this commit (see markGroupOfItem): remote
      // reads refresh the groups they rebuild themselves, and an update
      // applied without transforms runs none.
      const prevMap = prevEditorState._nodeMap;
      const isGroup = (n: LexicalNode | null | undefined) =>
        n !== null &&
        n !== undefined &&
        $isElementNode(n) &&
        getGroupSpec(klassOf(n)) !== null;
      editorState.read(() => {
        for (const [key, intentional] of dirtyElements) {
          if (!intentional) {
            continue;
          }
          const node = $getNodeByKey(key);
          if (!$isElementNode(node)) {
            continue;
          }
          if (isGroup(node)) {
            if (!transformed.has(key)) {
              localKeys.add(key);
            }
            continue;
          }
          // An item that starts or stops holding a nested list.
          const parent = node.getParent();
          if (!isGroup(parent)) {
            continue;
          }
          const prev = prevMap.get(key);
          const wasWrapper =
            prev !== undefined &&
            $isElementNode(prev) &&
            prev.__first !== null &&
            isGroup(prevMap.get(prev.__first));
          if (
            wasWrapper !== isGroup(node.getFirstChild()) &&
            !transformed.has(parent!.getKey())
          ) {
            localKeys.add(parent!.getKey());
          }
        }
      });
    }
    // The binding's run of the update Lexical made for a registered
    // transform (see runRegistrationPasses), or one Lexical committed itself
    // (registered while the binding did not write).
    const registration =
      this.isRegistrationPass(dirtyElements, dirtyLeaves, prevEditorState) ||
      tags.has(REGISTRATION_TAG);
    if (refresh && !registration) {
      // See $refreshGroups: only users' own edits write.
      this.state.refresh.clear();
      return;
    }
    if (
      this._status !== 'active' ||
      remote ||
      tags.has(SKIP_COLLAB_TAG) ||
      (dirtyElements.size === 0 && dirtyLeaves.size === 0)
    ) {
      return;
    }
    // What made the commit decides what is written. A follow-up is an
    // update every client that has a commit makes, no one's edit: the
    // binding's refresh of derived group fields, the update Lexical makes
    // when a transform is registered (it runs the transform over the whole
    // document), and BlockIdExtension's update that names the blocks a
    // commit left without an id (written whole, every client's would store
    // the lines it shows for content stored without markers). A follow-up
    // may set attributes or delete, never insert (see Writer#followUp). The
    // binding's own updates commit on their own (see runPending), so their
    // tags are theirs alone; an update another listener queues in the same
    // listener phase as the naming update is committed with it, and counts
    // as part of it.
    const naming = tags.has(BLOCK_ID_REPAIR_TAG);
    const followUp = refresh || registration || naming;
    const userEdit =
      !refresh && !registration && !naming && !tags.has(NORMALIZE_TAG);
    if (userEdit) {
      const replaced = $replacedNodes(
        dirtyElements,
        dirtyLeaves,
        prevEditorState,
        editorState,
      );
      if (replaced !== null) {
        [dirtyElements, dirtyLeaves] = replaced;
      }
    }
    if (registration && !naming) {
      // The update Lexical makes when a transform is registered (a plugin
      // that mounts, or mounts again, once the document is open) writes
      // nothing: opening a document is no one's edit. What its transforms
      // changed (a ragged table padded, its column widths recomputed) is
      // read again, so the editor shows the document; the author's next
      // edit of that content makes the change, and writes it.
      this.$refuseChanged(
        dirtyElements,
        dirtyLeaves,
        editorState,
        prevEditorState,
      );
      return;
    }
    if (this.refuseUnstorableSlots(editorState, dirtyElements.keys())) {
      return;
    }
    // What a user's update changed without Lexical's transforms (applied
    // with skipTransforms, or a state set whole) is normalized by the author
    // in an update of its own (see normalizeUntransformed).
    let untransformed = false;
    if (userEdit) {
      editorState.read(() => {
        for (const [key, intentional] of dirtyElements) {
          if (!intentional || transformed.has(key)) {
            continue;
          }
          const node = $getNodeByKey(key);
          if ($isElementNode(node) && node.isAttached()) {
            this.untransformed.set(key, null);
            untransformed = true;
          }
        }
        // The root's transforms run in every update that runs any: an
        // update in which they did not ran none on its text either.
        if (!transformed.has('root')) {
          for (const key of dirtyLeaves) {
            const node = $getNodeByKey(key);
            if ($isTextNode(node) && node.isAttached()) {
              this.untransformedText.add(key);
              untransformed = true;
            }
          }
        }
      });
    }
    const state = this.state;
    editorState.read(() => {
      const roles = new Roles(state);
      const plan = Writer.$plan(
        roles,
        dirtyElements,
        dirtyLeaves,
        prevEditorState,
      );
      const movedNodes = editorState._movedNodes;
      plan.moved =
        movedNodes === null ? null : movedNodes.get(prevEditorState._nodeMap);
      if (
        plan.structural.size === 0 &&
        plan.inline.size === 0 &&
        plan.lines.size === 0 &&
        plan.attrs.size === 0
      ) {
        return;
      }
      let writer: Writer | null = null;
      // A follow-up and BlockIdExtension's naming are no one's edit: out of
      // the undo history.
      const origin =
        userEdit || tags.has(NORMALIZE_TAG) ? this : this.followUpOrigin;
      const seq = this.remoteSeq;
      // The selection before this change, for the undo step it may start
      // (as relative positions on the content before it is written).
      this.writeCursor =
        origin === this && this._undoManager !== null
          ? prevEditorState.read(() => {
              try {
                return this.$captureCursor();
              } catch (_e) {
                return null;
              }
            })
          : null;
      try {
        this._doc.transact(tr => {
          writer = new Writer(state, roles, tr, prevEditorState, plan);
          writer.followUp = followUp;
          writer.$run();
        }, origin);
        // Kinds of types written for the first time, outside the undo
        // history (undoing the content must not forget how a type is stored).
        this._doc.transact(() => {
          this.recordPins(this._root, editorState, [
            ...dirtyElements.keys(),
            ...dirtyLeaves,
          ]);
        }, this.followUpOrigin);
      } catch (e) {
        // A write that fails part way must not leave the document silently
        // behind the editor: rewrite every container (a diff against the
        // shared content, so nothing a peer wrote is lost) in a fresh
        // transaction, and report it.
        writer = null;
        this.warn(
          RECOVERED_WRITE_WARNING,
          '@lexical/y: a write failed and the document was rewritten: ' +
            String(e instanceof Error ? e.message : e),
          {error: e},
        );
        try {
          this._doc.transact(tr => {
            const all: WritePlan = {
              attrs: new Set(state.yByKey.keys()),
              inline: new Set(),
              lines: new Set(state.unitByKey.keys()),
              removedText: plan.removedText,
              structural: new Set(),
            };
            for (const [key, cs] of state.csByKey) {
              (cs.kind === 'b' ? all.structural : all.inline).add(key);
            }
            const rewriter = new Writer(
              state,
              new Roles(state),
              tr,
              prevEditorState,
              all,
            );
            rewriter.rewriteAll = true;
            rewriter.followUp = followUp;
            rewriter.$run();
            this.noteRefused(rewriter, naming);
          }, origin);
        } catch (e2) {
          this._editor._onError(
            e2 instanceof Error ? e2 : new Error(String(e2)),
          );
        }
      }
      if (writer !== null) {
        this.noteRefused(writer, naming);
        if ((writer as Writer).refused.size > 0) {
          // Every container the refused change touched is read again, not
          // only those it was refused in: a change that moves content
          // between containers (adjacent lists in a line merged) leaves the
          // other one unlike the document too.
          for (const key of dirtyElements.keys()) {
            const cs = state.csByKey.get(key);
            if (cs !== undefined) {
              this.refused.add(cs);
            }
          }
        }
        if (!naming) {
          for (const key of (writer as Writer).refreshGroups) {
            if (!transformed.has(key)) {
              localKeys.add(key);
            }
          }
        }
      }
      if (userEdit) {
        this.rereads = 0;
      }
      // Containers holding blocks whose ids are settled after this write
      // (see toSettle): not compared until then.
      const settling = new Set<CS>();
      // The block ids this write stored (see Reader#$settleIds).
      if (writer !== null && state.blockIds !== null) {
        // The ids whose holders this write changed: an id it stored or
        // stopped storing on a block it wrote, the ids a block it removed
        // stored and showed, the ids a block now shows instead of another,
        // and a repeated id held by a block it changed (which may have moved
        // past another holder). Only those can show differently now, so
        // only those are checked (not every repeated id: the editor already
        // shows the others as a read settled them).
        const changed = new Set<string>();
        for (const key of dirtyElements.keys()) {
          const node = $getNodeByKey(key);
          if (node !== null && node.isAttached()) {
            const before = state.storedIdOf.get(key);
            const now = $storedIdNow(state, node);
            if (before !== now) {
              state.noteStoredId(key, now);
              if (before !== undefined) {
                changed.add(before);
              }
              if (typeof now === 'string') {
                changed.add(now);
              }
            }
          }
        }
        $touchChanged(
          state,
          dirtyElements,
          dirtyLeaves,
          prevEditorState._nodeMap,
          id => changed.add(id),
        );
        // An id that another block stores too (the editor held it on both),
        // or that a removed block held first: a reader gives the later holder
        // its derived id, or the remaining one the stored id. The editor is
        // settled the same way, in an update of the binding's own that is
        // not written (see $rereadRefused), so it shows what readers show.
        if (changed.size > 0) {
          const touched = new Set(state.touchedIds);
          const reader = new Reader(state);
          const unsettled = new Set(reader.$unsettled(changed));
          // Holders the check found removed (see Reader#$storers).
          for (const id of state.touchedIds) {
            if (!touched.has(id)) {
              unsettled.add(id);
            }
          }
          for (const id of unsettled) {
            this.toSettle.add(id);
          }
          // The blocks that store or derive them (see Reader#$claimants).
          for (const node of reader.$claimantsOf(unsettled)) {
            for (let n: LexicalNode | null = node; n !== null; ) {
              const cs = state.csByKey.get(n.getKey());
              if (cs !== undefined) {
                settling.add(cs);
                break;
              }
              n = n.getParent();
            }
          }
          if (this.toSettle.size > 0) {
            this.pending.add('reread');
          }
        }
      }
      // While a change made without Lexical's transforms waits for the
      // author's normalization, the editor is compared once that is written
      // (readers already build some of that normalization: adjacent equal
      // lists are one list).
      const check =
        this.options.selfCheck === true &&
        this.untransformed.size === 0 &&
        this.untransformedText.size === 0;
      // A remote change applied while this change was written (a provider
      // that delivers synchronously from an update handler) moved the shared
      // content on: the comparison would not be with what was written.
      if (
        check &&
        writer !== null &&
        this.remoteSeq === seq &&
        Math.random() < (this.options.selfCheckSample ?? 1)
      ) {
        const problems = $checkWrite(writer);
        // Whole containers: structural writes, and containers where a group
        // item's marker was written (group fields are shared by its items).
        // A container a follow-up changed in ways that are not written is
        // read again instead.
        const containers = new Set<CS>();
        for (const key of plan.structural) {
          const cs = state.csByKey.get(key);
          if (cs !== undefined) {
            containers.add(cs);
          }
        }
        for (const cs of (writer as Writer).groupWrites) {
          containers.add(cs);
        }
        for (const cs of containers) {
          if (
            !this.refused.has(cs) &&
            !settling.has(cs) &&
            sampleWholeContainer(cs)
          ) {
            pushAll(problems, checkContainer(state, cs, editorState));
          }
        }
        if (problems.length > 0) {
          this.warn(
            SELF_CHECK_WARNING,
            '@lexical/y self-check: ' + problems.slice(0, 5).join('; '),
            {problems, remote: false},
          );
        }
      }
    });
    if (!refresh) {
      if (localKeys.size > 0) {
        for (const key of localKeys) {
          this.localRefresh.add(key);
        }
        this.pending.add('refresh');
      }
    } else {
      state.refresh.clear();
    }
    if (untransformed) {
      for (const [key, anchor] of this.untransformed) {
        if (anchor === null) {
          const unit = state.unitByKey.get(key);
          this.untransformed.set(
            key,
            state.yByKey.get(key) ??
              (unit === undefined ? null : unit.end) ??
              null,
          );
        }
      }
      this.pending.add('normalize');
    }
  }

  /**
   * Queue the re-read of every container holding a node a commit changed
   * (its fields, NodeState, text or children), for a commit that is not
   * written (see onUpdate).
   */
  private $refuseChanged(
    dirtyElements: Map<NodeKey, boolean>,
    dirtyLeaves: Set<NodeKey>,
    editorState: EditorState,
    prevEditorState: EditorState,
  ): void {
    const state = this.state;
    const prevMap = prevEditorState._nodeMap;
    const nowMap = editorState._nodeMap;
    const shallow = (n: LexicalNode): string => {
      const json = n.exportJSON() as unknown as Record<string, unknown>;
      delete json.children;
      const slots = (n as {__slots?: null | Map<string, NodeKey>}).__slots;
      return JSON.stringify([
        json,
        slots === null || slots === undefined ? null : [...slots],
      ]);
    };
    const kids = (n: LexicalNode | undefined): string => {
      const out: NodeKey[] = [];
      if ($isElementNode(n)) {
        for (let c = n.__first; c !== null; ) {
          out.push(c);
          const cn: LexicalNode | undefined = nowMap.get(c) ?? prevMap.get(c);
          c = cn === undefined ? null : cn.__next;
        }
      }
      return out.join(',');
    };
    const changed: NodeKey[] = [];
    for (const key of [...dirtyElements.keys(), ...dirtyLeaves]) {
      const prev = prevMap.get(key);
      const now = nowMap.get(key);
      if (prev === now) {
        continue;
      }
      if (
        prev === undefined ||
        now === undefined ||
        prev.__parent !== now.__parent ||
        prevEditorState.read(() => shallow(prev)) !==
          editorState.read(() => shallow(now)) ||
        (() => {
          // Children of the previous version, walked in the previous map.
          const before: NodeKey[] = [];
          if ($isElementNode(prev)) {
            for (let c = prev.__first; c !== null; ) {
              before.push(c);
              const pc = prevMap.get(c);
              c = pc === undefined ? null : pc.__next;
            }
          }
          return before.join(',') !== kids(now);
        })()
      ) {
        changed.push(key);
      }
    }
    if (changed.length === 0) {
      return;
    }
    const containerOf = (key: NodeKey, map: Map<NodeKey, LexicalNode>) => {
      for (let n = map.get(key); n !== undefined; ) {
        // A slot's value is held by its host (its up-link), not a parent.
        const parent: NodeKey | null =
          n.__parent ?? (n as {__slotHost?: null | NodeKey}).__slotHost ?? null;
        if (parent === null) {
          return;
        }
        const cs =
          parent === 'root'
            ? state.containers.get(this._root)
            : state.csByKey.get(parent);
        if (cs !== undefined) {
          this.refused.add(cs);
          return;
        }
        n = map.get(parent);
      }
    };
    for (const key of changed) {
      const own = state.csByKey.get(key);
      if (own !== undefined) {
        this.refused.add(own);
      }
      containerOf(key, nowMap);
      containerOf(key, prevMap);
    }
    if (this.refused.size > 0) {
      this.pending.add('reread');
    }
  }

  /** Containers a write did not write a follow-up's change to (see refused). */
  private noteRefused(writer: Writer, naming: boolean): void {
    for (const cs of writer.refused) {
      this.refused.add(cs);
    }
    if (writer.refused.size > 0) {
      this.pending.add('reread');
      if (naming) {
        this.refusedNaming = true;
      }
    }
  }

  /**
   * Whether a commit holds the update Lexical makes when a node transform
   * is registered: it marks every node of the transform's type dirty, so
   * that the transform runs over the whole document (a plugin mounted once
   * the document has been read, such as a table plugin that pads ragged
   * tables). Every client that registers the transform makes that update,
   * so it is no one's edit (a follow-up): what it changes in content a
   * collaborator wrote is not written, and those containers are read again.
   */
  private isRegistrationPass(
    dirtyElements: Map<NodeKey, boolean>,
    dirtyLeaves: Set<NodeKey>,
    prevEditorState: EditorState,
  ): boolean {
    const added = this.noteTransforms();
    if (added.length === 0) {
      return false;
    }
    // Whether every node of each type that gained a transform is dirty. A
    // type whose nodes are not all dirty yet waits for its own update (a
    // plugin that registers transforms for several types makes one update
    // for each, and they commit one by one).
    const allDirty = new Map<string, boolean>();
    for (const [key, node] of prevEditorState._nodeMap) {
      const type = node.__type;
      if (added.includes(type)) {
        allDirty.set(
          type,
          allDirty.get(type) !== false &&
            (dirtyElements.has(key) || dirtyLeaves.has(key)),
        );
      }
    }
    let found = false;
    for (const [type, all] of allDirty) {
      if (all) {
        found = true;
      } else {
        this.registeredTypes.add(type);
      }
    }
    return found;
  }

  /**
   * Note the transforms each node type has; returns the types that gained
   * one since the last call (a transform registered again, as a plugin that
   * mounts again registers a new one, counts as gained).
   */
  private noteTransforms(): string[] {
    const added: string[] = [];
    for (const [type, info] of this._editor._nodes) {
      if (
        this.registeredTypes.has(type) ||
        this.gainedTransform(type, info.transforms)
      ) {
        added.push(type);
        this.transformSets.set(type, new Set(info.transforms));
      } else if (
        info.transforms.size !==
        (this.transformSets.get(type) ?? NO_TRANSFORMS).size
      ) {
        this.transformSets.set(type, new Set(info.transforms));
      }
    }
    this.registeredTypes.clear();
    return added;
  }

  /**
   * Note every node transform registered through the editor while the
   * binding runs: a transform registered again (a plugin that unregisters
   * and registers the same function when it mounts again, React's
   * StrictMode effects) leaves the type's transforms as they were, but
   * Lexical still runs them over every node of the type, which is a
   * registration pass like the first.
   *
   * While the binding writes, that pass (the update Lexical makes to mark
   * every node of the type dirty) never shares a commit with an edit:
   * Lexical runs it inside the running update (an app's), or queues it
   * where it is committed with whatever else is queued with it (an app's
   * edit queued by an update listener or an update's `onUpdate`), and the
   * commit would be taken for the pass, the edit never written. So it is
   * queued, not run, from any context (an update, a listener, a read,
   * outside any), taken off Lexical's queue, and run by the binding once the
   * editor is idle, as an update of its own (see runPending); an edit
   * still pending outside an update commits first. The transform itself is
   * registered at once, as without the binding: an update running then, or
   * made before the pass, runs it on what it changes, and is written as the
   * edit it is.
   */
  private noteRegistrations(): () => void {
    const editor = this._editor;
    const register = editor.registerNodeTransform;
    const registeredTypes = this.registeredTypes;
    const transformSets = this.transformSets;
    const binding = this;
    editor.registerNodeTransform = function (
      this: LexicalEditor,
      klass: Klass<LexicalNode>,
      listener: Transform<LexicalNode>,
    ) {
      if (binding._status !== 'active') {
        // Nothing is written yet (or at all): the pass commits as Lexical
        // makes it, and is noted for isRegistrationPass.
        registeredTypes.add(klass.getType());
        return register.call(this, klass, listener);
      }
      if (!editor._updating && !isCurrentlyReadOnlyMode()) {
        binding.commitPending();
      }
      const updating = editor._updating;
      const from = editor._updates.length;
      // Lexical queues an update made while one runs instead of running it.
      editor._updating = true;
      let dispose: () => void;
      try {
        dispose = register.call(this, klass, listener);
      } finally {
        editor._updating = updating;
      }
      const queued = editor._updates.splice(from);
      // The types that gained the transform are noted now, so that a commit
      // before the pass is not taken for it.
      for (const [type, info] of editor._nodes) {
        if (info.transforms.has(listener)) {
          transformSets.set(type, new Set(info.transforms));
        }
      }
      if (queued.length > 0) {
        for (const [fn] of queued) {
          binding.registrationPasses.push(fn);
        }
        binding.pending.add('register');
        // Not inside a read (an update must not run there). Once a pass ran
        // in this task, the next ones wait for a microtask and run as one:
        // transforms registered in a row (a plugin host enabling plugins in
        // a loop) all run over the document, in one update, as Lexical
        // commits their updates together.
        binding.schedulePending(
          isCurrentlyReadOnlyMode() || binding.registrationRuns > 0,
        );
      }
      return dispose;
    } as typeof register;
    return () => {
      editor.registerNodeTransform = register;
    };
  }

  /**
   * Run the updates Lexical made for registered transforms (see
   * noteRegistrations) as one update of their own, from runPending (the
   * editor is idle, so it commits alone). It is no one's edit: tagged so
   * (see onUpdate, where what its transforms changed is read again). It
   * stays Lexical's update, tagged as Lexical tags it, not
   * COLLABORATION_TAG: BlockIdExtension names the blocks it changes in it,
   * rather than in a naming update of its own, which an app listener's edit
   * queued in the same listener phase would be committed with (and taken
   * for).
   */
  private runRegistrationPasses(): void {
    const passes = this.registrationPasses.splice(0);
    if (passes.length === 0) {
      return;
    }
    if (this.registrationRuns++ === 0) {
      setTimeout(() => {
        this.registrationRuns = 0;
      }, 0);
    }
    if (this.registrationRuns > MAX_REGISTRATION_RUNS) {
      if (process.env.NODE_ENV !== 'production') {
        console.warn(
          `@lexical/y: more than ${MAX_REGISTRATION_RUNS} updates for registered transforms ran before the event loop turned (transforms registered in more than ${MAX_REGISTRATION_RUNS} microtasks of one task, or a listener that registers a transform after every commit); the update of a transform registered since is dropped, so it does not run over the existing document.`,
        );
      }
      return;
    }
    this._editor.update(
      () => {
        for (const pass of passes) {
          pass();
        }
      },
      {discrete: true, tag: [HISTORY_MERGE_TAG, REGISTRATION_TAG]},
    );
  }

  /** Whether `transforms` holds one type `type` did not have when noted. */
  private gainedTransform(
    type: string,
    transforms: ReadonlySet<Transform<LexicalNode>>,
  ): boolean {
    const noted = this.transformSets.get(type) ?? NO_TRANSFORMS;
    for (const t of transforms) {
      if (!noted.has(t)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Commit the local updates still pending (an editor.update() made in the
   * same task, or one a listener of the last commit queued), so that an
   * update the binding makes next (a read) commits on its own: an update
   * still pending would be committed with it, and take its tags. Committing
   * one can leave another pending (its listeners queue one).
   */
  private commitPending(): void {
    const editor = this._editor;
    for (
      let i = 0;
      i < 16 && editor._pendingEditorState !== null && !editor._updating;
      i++
    ) {
      editor.update(() => {}, {discrete: true});
    }
  }

  /**
   * Whether a local update that changes content commits now, as one with
   * `discrete: true` does, instead of in a microtask (where several updates
   * made in one task are committed, and written, together): once a commit
   * was made in the task (an update an app's listener queues: a provider
   * that applies a remote change in the same task would apply it before
   * that update is written, which would then be written at positions
   * computed without it), while the binding has updates of its own waiting
   * for the editor, which must not share a commit with an app's (see
   * runPending), and while a transform
   * registered since the last commit waits for the update Lexical makes to
   * run it over the whole document (see isRegistrationPass), which commits
   * on its own so that an edit made in the same task is not committed with
   * it.
   */
  private commitsAtOnce(): boolean {
    if (this.task.committed || this.pending.size > 0 || this.pendingScheduled) {
      return true;
    }
    if (this.registeredTypes.size > 0) {
      return true;
    }
    for (const [type, info] of this._editor._nodes) {
      if (this.gainedTransform(type, info.transforms)) {
        return true;
      }
    }
    return false;
  }

  /**
   * @internal Run the binding's own updates that wait for the editor to be
   * idle (see runPending) now, instead of in a microtask: for the headless
   * helpers, which commit the editor's pending updates themselves and
   * encode the document right after an edit. Returns whether any of them
   * still waits (the editor is not idle: a listener queued an update).
   */
  flushPending(): boolean {
    return this.guard(() => {
      this.runPending();
      return this.pending.size > 0;
    });
  }

  /** Whether no update is running, queued or pending. */
  private isIdle(): boolean {
    const editor = this._editor;
    return (
      !editor._updating &&
      editor._updates.length === 0 &&
      editor._pendingEditorState === null
    );
  }

  /**
   * Run the binding's pending updates (see runPending) now if the editor is
   * idle (and not `later`), else in a microtask; if the editor is still busy
   * then, the update listener schedules them again after the next commit.
   */
  private schedulePending(later = false): void {
    if (this.pending.size === 0) {
      return;
    }
    if (!later && this.isIdle()) {
      this.runPending();
    } else if (!this.pendingScheduled) {
      this.pendingScheduled = true;
      queueMicrotask(() => {
        this.pendingScheduled = false;
        this.guard(() => this.runPending());
      });
    }
  }

  /**
   * The binding's own updates: showing what was held back during a
   * composition, reading containers again after a follow-up's change was
   * not written, the author's normalization of an update that ran no
   * transforms, the refresh after a local change, and Lexical's update for
   * a registered transform (see noteRegistrations). Each commits as an
   * update of its own. Lexical runs the updates queued during one listener
   * phase as one commit, with their tags and options merged, so an update
   * queued from the binding's listener would share a commit with whatever
   * another listener queued (an app's edit), and the commit could no longer
   * tell whose its changes are: an app's edit merged into a read would never
   * be written, and one merged into the refresh would not be written either.
   * So they wait until the editor is idle: in a microtask after the listener
   * phase, or when a remote transaction arrives, once what it brings has
   * been read (never before: a write then would delete what the editor does
   * not show yet). The author's normalization also waits for a composition
   * to end, and is first tried right away (see queueNormalize).
   */
  private runPending(): void {
    if (this.disposers.length === 0) {
      this.pending.clear();
      this.localRefresh.clear();
      this.remoteRefresh.clear();
      this.refused.clear();
      this.toSettle.clear();
      this.untransformed.clear();
      this.untransformedText.clear();
      this.registrationPasses.length = 0;
      return;
    }
    for (;;) {
      if (!this.isIdle()) {
        return;
      }
      const work = PENDING_ORDER.find(
        w =>
          this.pending.has(w) &&
          (w !== 'normalize' || this._editor._compositionKey === null),
      );
      if (work === undefined) {
        return;
      }
      this.pending.delete(work);
      withPins(this._pins, () => {
        if (work === 'hidden') {
          this.flushHidden();
        } else if (work === 'reread') {
          this.rereadRefused();
        } else if (work === 'normalize') {
          this.normalizeUntransformed();
        } else if (work === 'register') {
          this.runRegistrationPasses();
        } else {
          this.flushRefresh(true, this.remoteRefresh);
          this.flushRefresh(false, this.localRefresh);
        }
      });
    }
  }

  /**
   * Read again the containers where a follow-up changed what it may not
   * write (see Writer#followUp): the editor goes back to what is stored,
   * so that it never differs from the document (and from every other
   * client). Normally this runs as the next update (see queueReread); here
   * when the editor is idle (see runPending).
   */
  private rereadRefused(): void {
    let after: (() => void) | null = null;
    this._editor.update(
      () => {
        after = this.$rereadRefused();
      },
      {discrete: true, skipTransforms: true},
    );
    if (after !== null) {
      (after as () => void)();
    }
  }

  /**
   * Queue the re-read of the containers a follow-up changed in ways that are
   * not written (see rereadRefused) as the next update, from the update
   * listener that found them: at the front of Lexical's queue, so that no
   * other update (one another listener queued in the same listener phase,
   * or one the app makes later in the same task) is applied to an editor
   * that still shows the change, and written against it. The updates queued
   * behind it, which Lexical would run in the same update, run right after
   * its commit, in their own.
   */
  private queueReread(): void {
    const editor = this._editor;
    if (
      !this.pending.has('reread') ||
      !editor._updating ||
      editor._updates.some(([fn]) => fn === this.rereadUpdate)
    ) {
      return;
    }
    editor._updates.unshift([
      this.rereadUpdate,
      {discrete: true, skipTransforms: true},
    ]);
  }

  /** The update queueReread queues. */
  private readonly rereadUpdate = (): void => {
    const editor = this._editor;
    const later = editor._updates.splice(0);
    let done = false;
    try {
      this.guard(() =>
        withPins(this._pins, () => {
          const after = this.$rereadRefused();
          if (after !== null || later.length > 0) {
            $onUpdate(() => {
              for (const [fn, options] of later) {
                editor.update(fn, options);
              }
              if (after !== null) {
                this.guard(() => withPins(this._pins, after));
              }
            });
          }
        }),
      );
      done = true;
    } finally {
      if (!done) {
        // The update fails: what was queued behind it runs as Lexical runs
        // queued updates.
        spliceAll(editor._updates, 0, 0, later);
      }
    }
  };

  /**
   * The re-read itself (see rereadRefused), inside an update; returns what
   * runs once it has committed, if anything.
   */
  private $rereadRefused(): (() => void) | null {
    const list = [...this.refused].filter(
      cs => this.state.containers.get(cs.y) === cs,
    );
    const naming = this.refusedNaming;
    const settle = [...this.toSettle];
    this.refused.clear();
    this.toSettle.clear();
    this.refusedNaming = false;
    this.pending.delete('reread');
    if (list.length === 0 && settle.length === 0) {
      return null;
    }
    const last = ++this.rereads > MAX_REREADS;
    for (const tag of REMOTE_TAGS) {
      $addUpdateTag(tag);
    }
    // The re-read of a naming update's change is tagged as that update, so
    // that BlockIdExtension does not make it again on the content read.
    // So is a last read (below).
    if (naming || last) {
      $addUpdateTag(BLOCK_ID_REPAIR_TAG);
    }
    const cursor = this.$cursorBeforeRead();
    try {
      const reader = new Reader(this.state);
      for (const cs of list) {
        const el = cs.y === this._root ? $getRoot() : $getNodeByKey(cs.key);
        if ($isElementNode(el) && el.isAttached()) {
          reader.$readFull(cs, el);
        }
      }
      reader.$settle(settle);
      this.$selectionAfterRead(cursor);
    } catch (e) {
      this.warn(
        RECOVERED_READ_WARNING,
        `@lexical/y: a change could not be read again and the editor was rebuilt from the document: ${String(
          e instanceof Error ? e.message : e,
        )}`,
        {error: e},
      );
      this.$rebuild();
    }
    this.$quietSelection();
    if (last) {
      // A transform that changes the same content each time it runs (a
      // list's own transforms in every refresh, say): a last read, with no
      // refresh after it, so that the editor still shows the document.
      if (process.env.NODE_ENV !== 'production') {
        console.warn(
          '@lexical/y: follow-ups keep changing content the binding does not write; the editor reads it again without refreshing it.',
        );
      }
      // Nor the refresh that would make the change again.
      this.state.refresh.clear();
      this.localRefresh.clear();
      this.remoteRefresh.clear();
      this.pending.delete('refresh');
      return () => this.checkUnknownTypes();
    }
    return () => {
      this.checkUnknownTypes();
      this.flushRefresh(true);
    };
  }

  /**
   * The author's normalization of its own update that ran no transforms
   * (`editor.update(fn, {skipTransforms: true})`, or `setEditorState` with a
   * state the editor did not parse): an update that marks what it changed
   * dirty, so that Lexical's transforms run on it, and calls
   * NodeStructureExtension's normalization on it (as code that applies an
   * update with skipTransforms does). Only the author normalizes, under its
   * own client id, as part of its edit (in the same undo step); readers show
   * the update as it was written until then. It is queued from the update
   * listener, so that it runs right after the update, before a remote change
   * can be read (which could give the nodes it normalizes new ones); not
   * while composing. Lexical commits an update queued there together with
   * any other update queued in the same listener phase: then it does
   * nothing (it is queued with no tags, so that it adds nothing to that
   * commit) and waits for the next phase, or for the editor to be idle (see
   * runPending), so that its commit holds only its own changes.
   */
  private queueNormalize(): void {
    if (
      this.normalizeQueued ||
      !this.pending.has('normalize') ||
      this._editor._compositionKey !== null
    ) {
      return;
    }
    this.normalizeQueued = true;
    this._editor.update(
      () => {
        this.normalizeQueued = false;
        const editor = this._editor;
        // Not while the editor still shows a change the binding did not
        // write (see rereadRefused): the normalization would find it done.
        if (
          this.pending.has('normalize') &&
          !this.pending.has('reread') &&
          editor._updates.length === 0 &&
          editor._dirtyElements.size === 0 &&
          editor._dirtyLeaves.size === 0 &&
          editor._updateTags.size === 0
        ) {
          this.pending.delete('normalize');
          this.$normalize();
        }
      },
      {discrete: true},
    );
  }

  /** The author's normalization, once the editor is idle (see runPending). */
  private normalizeUntransformed(): void {
    this._editor.update(() => this.$normalize(), {discrete: true});
  }

  /** The author's normalization itself, inside an update. */
  private $normalize(): void {
    if (
      this._status !== 'active' ||
      (this.untransformed.size === 0 && this.untransformedText.size === 0)
    ) {
      this.untransformed.clear();
      this.untransformedText.clear();
      return;
    }
    const entries = [...this.untransformed];
    const texts = [...this.untransformedText];
    this.untransformed.clear();
    this.untransformedText.clear();
    $addUpdateTag(HISTORY_MERGE_TAG);
    $addUpdateTag(NORMALIZE_TAG);
    for (const key of texts) {
      const node = $getNodeByKey(key);
      if ($isTextNode(node) && node.isAttached()) {
        node.markDirty();
      }
    }
    // Each element, found by what stores it if a remote change read since
    // gave it a new node, and the element that holds it now.
    const nodes = new Set<ElementNode>();
    for (const [key, anchor] of entries) {
      let node = $getNodeByKey(key);
      if (!$isElementNode(node) || !node.isAttached()) {
        node = this.$nodeStoredBy(anchor);
      }
      if ($isElementNode(node) && node.isAttached()) {
        nodes.add(node);
        const parent = node.getParent();
        if (parent !== null) {
          nodes.add(parent);
        }
      }
    }
    for (const node of nodes) {
      node.markDirty();
      // The root's own normalization runs in every update (it wraps inline
      // content); the whole document is not.
      if (!$isRootNode(node)) {
        INTERNAL_$normalizeNodeStructure(node);
      }
    }
  }

  /**
   * At the end of a read (an update with skipTransforms that shows what is
   * stored): when its selection changed, Lexical extends the commit with the
   * selection change command, and runs every node transform over the
   * update's changes in it, whatever the update's options: over the content
   * the read brought (a table transform pads a ragged table), which the
   * editor would then show unlike the document, and which the binding would
   * not write. So the read's selection counts as notified, and the command
   * is dispatched once the read has committed, in an update of its own.
   * Lexical skips the notification itself where it would not run (headless,
   * no root element).
   */
  private $quietSelection(): void {
    const editor = this._editor;
    $clampSelection();
    const selection = $getSelection();
    const previous = editor._lastNotifiedSelection;
    if (selection === null ? previous === null : selection.is(previous)) {
      return;
    }
    const root = editor._rootElement;
    if (
      (selection === null || $isRangeSelection(selection)) &&
      (editor._headless || root === null || !root.isConnected)
    ) {
      return;
    }
    editor._lastNotifiedSelection =
      selection === null ? null : selection.clone();
    $onUpdate(() => {
      editor.update(() => {
        editor.dispatchCommand(SELECTION_CHANGE_COMMAND, undefined);
      });
    });
  }

  /** The node a shared node or a line's marker stores now, if any. */
  private $nodeStoredBy(anchor: YNode | Item | null): LexicalNode | null {
    if (anchor === null) {
      return null;
    }
    if (anchor instanceof YNode) {
      const key = this.state.keyByY.get(anchor);
      return key === undefined ? null : $getNodeByKey(key);
    }
    const unit = this.state.unitByEnd.get(anchor);
    return unit === undefined || unit.key === null
      ? null
      : $getNodeByKey(unit.key);
  }

  // -------------------------------------------------------------------------
  // Undo

  /**
   * Undo keeps a container a peer has put content in, whole: with its
   * fields and the undoing client's own content in it (deleting those would
   * leave a malformed container).
   */
  private isKeptByUndo(item: Item): boolean {
    // A container this undo also restores elsewhere was moved (deleted and
    // written again): keeping the new copy would duplicate it.
    const moved = (it: Item): boolean =>
      this.restoring !== null && this.restoring.has(nameOf(it));
    if (isNonEmptyContainer(item, this.undoCache)) {
      return !moved(item);
    }
    for (
      let t: unknown = item.parent;
      t instanceof YNode && t !== this._root;
      t = t._item === null ? null : t._item.parent
    ) {
      // Only a container this undo deletes (one it inserted): the content
      // of other containers is undone as usual.
      if (
        t._item !== null &&
        this.removing !== null &&
        this.removing.has(t._item) &&
        isNonEmptyContainer(t._item, this.undoCache)
      ) {
        return !moved(t._item);
      }
    }
    return false;
  }

  /**
   * Undo this client's last change in the document (collaborative undo).
   * Returns whether there was one; false while the binding is not active.
   */
  undo(): boolean {
    return this.undoOrRedo(true);
  }

  /** Redo what `undo` undid; see `undo`. */
  redo(): boolean {
    return this.undoOrRedo(false);
  }

  /**
   * Called while the editor is updating (from a command handler such as
   * UNDO_COMMAND's, inside an update or its `$onUpdate`, from a listener),
   * the undo or redo runs in an update of its own, with the binding's
   * options (no transforms, tagged as a collaborator's change), as the next
   * update: right after the running update, which then commits at once (see
   * queueFirst). Applied inside the running update, it would be committed
   * with that update's options and tags, and Lexical's transforms (list
   * numbering) would run over the part it had read. Returns whether there
   * was a step to undo or redo.
   */
  private undoOrRedo(undo: boolean): boolean {
    const um = this._undoManager;
    // Nothing is written while the binding is not active (see
    // YBindingStatus): an undo or redo would write.
    if (um === null || this._status !== 'active') {
      return false;
    }
    const editor = this._editor;
    if (!editor._updating) {
      return this.applyUndo(um, undo);
    }
    if (!(undo ? um.canUndo() : um.canRedo())) {
      return false;
    }
    const run = () =>
      this.queueFirst(
        () => {
          this.applyUndo(um, undo);
        },
        {discrete: true, skipTransforms: true, tag: REMOTE_TAGS},
      );
    if (editor._pendingEditorState !== null) {
      // Inside an update: after it commits.
      $flushSyncAfterUpdate();
      $onUpdate(() => this.guard(run));
    } else {
      run();
    }
    return true;
  }

  private applyUndo(um: UndoManager, undo: boolean): boolean {
    const stack = undo ? um.undoStack : um.redoStack;
    this.undoCache = new WeakMap();
    this.scanStackItem(stack);
    const top = stack[stack.length - 1];
    this.stepCursor =
      top === undefined ? null : ((top.meta.get(this) as YCursor) ?? null);
    try {
      return (undo ? um.undo() : um.redo()) !== null;
    } finally {
      this.restoring = null;
      this.removing = null;
      this.stepCursor = null;
    }
  }

  /**
   * Queue `fn` as the next update, at the front of Lexical's queue (call
   * while the editor is updating). The updates queued behind it, which
   * Lexical would run as part of the same update, run right after its
   * commit, in their own.
   */
  private queueFirst(
    fn: () => void,
    options: {discrete: true; skipTransforms: true; tag?: string[]},
  ): void {
    const editor = this._editor;
    editor._updates.unshift([
      () => {
        const later = editor._updates.splice(0);
        let done = false;
        try {
          this.guard(() => withPins(this._pins, fn));
          if (later.length > 0) {
            $onUpdate(() => {
              for (const [f, o] of later) {
                editor.update(f, o);
              }
            });
          }
          done = true;
        } finally {
          if (!done) {
            spliceAll(editor._updates, 0, 0, later);
          }
        }
      },
      options,
    ]);
  }

  /**
   * The stored nodes the next stack item restores (by name) and deletes
   * (items), for the undo delete filter.
   */
  private scanStackItem(stack: UndoManager['undoStack']): void {
    const top = stack[stack.length - 1];
    this.restoring = null;
    this.removing = null;
    if (top === undefined) {
      return;
    }
    const names = new Set<string>();
    const removing = new Set<Item>();
    const isStored = (s: unknown): s is Item => {
      if (!(s instanceof Item) || !(s.content instanceof ContentType)) {
        return false;
      }
      const name = nameOf(s);
      return name !== MARKER && name !== RUN_END;
    };
    this._doc.transact(tr => {
      iterateStructsByIdSet(tr, top.deletes, s => {
        if (isStored(s)) {
          names.add(nameOf(s));
        }
      });
      iterateStructsByIdSet(tr, top.inserts, s => {
        if (isStored(s)) {
          removing.add(s);
        }
      });
    }, this.scanOrigin);
    this.restoring = names;
    this.removing = removing;
  }

  // -------------------------------------------------------------------------
  // Cursors

  /** The local selection as relative positions (JSON), or null. */
  getCursor(): YCursor | null {
    return this._editor.getEditorState().read(() => {
      try {
        return this.$captureCursor();
      } catch (_e) {
        // A selection the editor itself left invalid: no cursor.
        return null;
      }
    });
  }

  /**
   * The current selection as relative positions. A collapsed caret is
   * anchored to the character on its left, so that it stays after what the
   * user just typed when a peer inserts at the same place; a range is
   * anchored to its first and last characters, so it does not grow over
   * concurrent inserts at its edges.
   */
  private $captureCursor(state = this.state): YCursor | null {
    const selection = $getSelection();
    if (!$isRangeSelection(selection)) {
      return null;
    }
    const collapsed = selection.isCollapsed();
    const backward = selection.isBackward();
    const anchor = this.$relativePosition(
      selection.anchor,
      collapsed || backward,
      state,
    );
    const focus = this.$relativePosition(
      selection.focus,
      collapsed || !backward,
      state,
    );
    return anchor === null || focus === null ? null : {anchor, focus};
  }

  /**
   * Inside an update, before a full read of containers (see
   * Reader#$readFull), which can give the lines and wrappers the selection
   * is in other nodes: the selection as relative positions, or null.
   */
  private $cursorBeforeRead(state = this.state): YCursor | null {
    try {
      return this.$captureCursor(state);
    } catch (_e) {
      return null;
    }
  }

  /**
   * After a full read: put back the selection captured before it (see
   * $cursorBeforeRead), a caret staying a caret, and drop what still names
   * a removed node.
   */
  private $selectionAfterRead(cursor: YCursor | null): void {
    if (cursor !== null) {
      this.$restoreSelection(cursor, true);
    }
    $clampSelection();
    this.$caretOnText();
  }

  /**
   * A caret a read leaves on a block element that is not a line (a list, a
   * list item holding a nested list, a table, a box) goes to the nearest
   * text position inside it: the end of what is before it there, else the
   * start of what is after. Typing on such an element is dropped (or lands
   * inside its structure), and Backspace deletes structure (a nested list
   * of other users' text).
   */
  private $caretOnText(): void {
    const selection = $getSelection();
    if (
      !$isRangeSelection(selection) ||
      !selection.isCollapsed() ||
      selection.anchor.type !== 'element'
    ) {
      return;
    }
    const node = selection.anchor.getNode();
    if (
      !$isElementNode(node) ||
      node.isInline() ||
      this.state.unitByKey.has(node.getKey())
    ) {
      return;
    }
    const cs = this.state.csByKey.get(node.getKey());
    if (cs !== undefined && cs.kind === 'i') {
      return;
    }
    const offset = selection.anchor.offset;
    const before = offset > 0 ? node.getChildAtIndex(offset - 1) : null;
    const after = node.getChildAtIndex(offset);
    if ($isElementNode(before)) {
      before.selectEnd();
    } else if ($isElementNode(after)) {
      after.selectStart();
    }
  }

  /** Resolve a cursor to Lexical points (call inside a read or update). */
  $resolveCursor(
    cursor: YCursor,
  ): {anchor: PointType; focus: PointType} | null {
    const anchor = this.$resolvePosition(cursor.anchor);
    const focus = this.$resolvePosition(cursor.focus);
    if (anchor === null || focus === null) {
      return null;
    }
    const selection = $createRangeSelection();
    selection.anchor.set(anchor.key, anchor.offset, anchor.type);
    selection.focus.set(focus.key, focus.offset, focus.type);
    return {anchor: selection.anchor, focus: selection.focus};
  }

  /**
   * Map the local selection through a remote change: resolve the cursor
   * captured before the transaction; points that cannot be resolved are
   * clamped to their node. With `keepCaret`, a caret is never widened into a
   * range: when the editor shows a caret but the cursor was a range (a local
   * update committed after the cursor was captured, such as an arrow key
   * that collapsed a selection), the caret stays where it is (clamped), as a
   * Backspace would otherwise delete a range the user no longer selects.
   */
  private $restoreSelection(cursor: YCursor, keepCaret = false): void {
    const current = $getSelection();
    if (current !== null && !$isRangeSelection(current)) {
      return;
    }
    let selection: RangeSelection | null = current;
    const anchor = this.$resolvePosition(cursor.anchor);
    const focus = this.$resolvePosition(cursor.focus);
    const widens =
      keepCaret &&
      selection !== null &&
      selection.isCollapsed() &&
      anchor !== null &&
      focus !== null &&
      (anchor.key !== focus.key ||
        anchor.offset !== focus.offset ||
        anchor.type !== focus.type);
    if (anchor !== null && focus !== null && !widens) {
      if (selection === null) {
        selection = $createRangeSelection();
        $setSelection(selection);
      }
      const same = (
        p: PointType,
        q: {key: NodeKey; offset: number; type: 'text' | 'element'},
      ) => p.key === q.key && p.offset === q.offset && p.type === q.type;
      if (!same(selection.anchor, anchor) || !same(selection.focus, focus)) {
        selection.anchor.set(anchor.key, anchor.offset, anchor.type);
        selection.focus.set(focus.key, focus.offset, focus.type);
      }
      return;
    }
    if (selection !== null) {
      for (const point of [selection.anchor, selection.focus]) {
        const node = $getNodeByKey(point.key);
        if (node === null || !node.isAttached()) {
          $setSelection(null);
          return;
        }
        const size = $isTextNode(node)
          ? node.getTextContentSize()
          : $isElementNode(node)
            ? node.getChildrenSize()
            : 0;
        if (point.offset > size) {
          point.set(point.key, size, point.type);
        }
      }
    }
  }

  private $relativePosition(
    point: PointType,
    preferLeft: boolean,
    state = this.state,
  ): unknown {
    const node = point.getNode();
    // Find the line (or inline container) and the atom offset within it.
    let offset = 0;
    let owner: ElementNode | null = null;
    let target: LexicalNode = node;
    if ($isTextNode(node)) {
      offset = point.offset;
    } else if ($isElementNode(node)) {
      const child = node.getChildAtIndex(point.offset);
      if (child === null) {
        // At the end of an element: the end of a line, or of the content of
        // a container or wrapper whose last child is the target.
        const last = node.getLastChild();
        if (last === null) {
          const unit = state.unitByKey.get(node.getKey());
          return unit !== undefined && unit.end !== null
            ? relativePositionToJSON(
                new RelativePosition(null, null, unit.end.id, 0),
              )
            : null;
        }
        target = last;
        offset = $atomSize(last);
      } else {
        target = child;
      }
      preferLeft = false;
    }
    const parent = $ownerOf(target);
    if (parent === null) {
      return null;
    }
    owner = parent;
    offset += $atomsBefore(parent, target);
    const unit = state.unitByKey.get(owner.getKey());
    let start: Item | null;
    if (unit !== undefined && unit.end !== null) {
      const left = prevLiveEnd(unit.end);
      start = left === null ? unit.cs.y._start : left.right;
    } else {
      const cs = state.csByKey.get(owner.getKey());
      if (cs === undefined || cs.kind !== 'i') {
        return null;
      }
      start = cs.y._start;
    }
    const at = (it: Item, d: number, assoc: number) =>
      relativePositionToJSON(
        new RelativePosition(
          null,
          null,
          {client: it.id.client, clock: it.id.clock + d} as Item['id'],
          assoc,
        ),
      );
    // Offsets count what the editor shows (not hidden remote content).
    const hidden = state.hidden;
    const unitAt = (it: Item, shown: number) =>
      hidden === null ? shown : hidden.unitAt(it, shown);
    let lastLive: Item | null = null;
    let lastLen = 0;
    for (let it = start; it !== null; it = it.right) {
      const len = shownLength(it, hidden);
      if (len === 0) {
        if (isEndItem(it) && !it.deleted) {
          break;
        }
        continue;
      }
      if (offset < len) {
        if (preferLeft && offset > 0) {
          return at(it, unitAt(it, offset - 1), -1);
        }
        if (preferLeft && offset === 0 && lastLive !== null) {
          return at(lastLive, unitAt(lastLive, lastLen - 1), -1);
        }
        return at(it, unitAt(it, offset), 0);
      }
      offset -= len;
      lastLive = it;
      lastLen = len;
      if (isEndItem(it)) {
        break;
      }
    }
    return null;
  }

  /**
   * See $resolvePosition: the nearest text position to a position in a
   * block container whose line is gone. The end of the nearest line before
   * it in the container, else the start of the nearest one after; where the
   * container has no other line, the nearest line inside a block node next
   * to it (the end of a table's last cell). Never a point on a block node
   * itself (a table, a list, a box), where typing is dropped and Backspace
   * deletes structure. No line is created: with none, there is no point.
   */
  private $nearestLinePoint(
    item: Item,
  ): {key: NodeKey; offset: number; type: 'text' | 'element'} | null {
    const state = this.state;
    const shown = (key: NodeKey): LexicalNode | null => {
      const node = $getNodeByKey(key);
      return node !== null && node.isAttached() ? node : null;
    };
    // The last (or first) line in a stored block node, depth first.
    const lineIn = (
      y: YNode,
      last: boolean,
      depth: number,
    ): LexicalNode | null => {
      const cs = state.containers.get(y);
      if (cs === undefined || depth > 64) {
        return null;
      }
      if (cs.kind === 'i') {
        return shown(cs.key);
      }
      const units = last ? [...cs.units].reverse() : cs.units;
      for (const u of units) {
        const found =
          u.key === null
            ? null
            : u.kind === 'line' || u.kind === 'implicit'
              ? shown(u.key)
              : u.kind === 'node' && u.end !== null && !u.end.deleted
                ? lineIn(typeOf(u.end), last, depth + 1)
                : null;
        if (found !== null) {
          return found;
        }
      }
      return null;
    };
    const lineAt = (
      it: Item,
      last: boolean,
      inside: boolean,
    ): LexicalNode | null => {
      if (it.deleted || !isEndItem(it)) {
        return null;
      }
      const unit = state.unitByEnd.get(it);
      if (unit === undefined || unit.key === null) {
        return null;
      }
      return unit.kind === 'line'
        ? shown(unit.key)
        : unit.kind === 'node' && inside
          ? lineIn(typeOf(it), last, 0)
          : null;
    };
    for (const inside of [false, true]) {
      for (let it = item.left; it !== null; it = it.left) {
        const line = lineAt(it, true, inside);
        if (line !== null) {
          return $lineEndPoint(line, true);
        }
      }
      for (let it: Item | null = item; it !== null; it = it.right) {
        const line = lineAt(it, false, inside);
        if (line !== null) {
          return $lineEndPoint(line, false);
        }
      }
    }
    return null;
  }

  private $resolvePosition(
    json: unknown,
  ): {key: NodeKey; offset: number; type: 'text' | 'element'} | null {
    const rel = createRelativePositionFromJSON(json);
    if (rel.item === null) {
      return null;
    }
    const store = this._doc.store;
    if (store.getClock(rel.item.client) <= rel.item.clock) {
      return null;
    }
    let found = store.getItem(rel.item);
    if (!(found instanceof Item)) {
      return null;
    }
    let diff = rel.item.clock - found.id.clock;
    // A character an undo or redo restored: the copy that restored it (the
    // deleted original points to it).
    while (found.deleted && found.redone !== null) {
      const next = createID(found.redone.client, found.redone.clock + diff);
      if (store.getClock(next.client) <= next.clock) {
        break;
      }
      const copy = store.getItem(next);
      if (!(copy instanceof Item)) {
        break;
      }
      diff = next.clock - copy.id.clock;
      found = copy;
    }
    let item: Item | null = found;
    if (rel.assoc < 0) {
      // After a character: before the next live one.
      if (!found.deleted && found.countable && diff + 1 < found.length) {
        diff += 1;
      } else {
        let p: Item | null = found;
        if (found.deleted || !found.countable) {
          // The character is gone: after the nearest live one on its left.
          p = found.left;
          while (p !== null && (p.deleted || !p.countable)) {
            p = p.left;
          }
        }
        item = p === null ? (found.parent as YNode)._start : p.right;
        diff = 0;
      }
    }
    const hidden = this.state.hidden;
    while (item !== null && shownLength(item, hidden) === 0) {
      item = item.right;
      diff = 0;
    }
    if (item === null) {
      // The line it was in is gone and was the last of its block container
      // (after a list or a table): the nearest line before it.
      const cs = this.state.containers.get(found.parent as YNode);
      return found.deleted && cs !== undefined && cs.kind === 'b'
        ? this.$nearestLinePoint(found)
        : null;
    }
    // Walk to the unit end; count atoms from the unit start.
    let end: Item | null = item;
    while (end !== null && (end.deleted || !isEndItem(end))) {
      end = end.right;
    }
    const parentY = item.parent as YNode;
    const unit = end === null ? undefined : this.state.unitByEnd.get(end);
    let ownerKey: NodeKey | undefined;
    let start: Item | null;
    if (unit !== undefined && unit.key !== null && unit.kind === 'line') {
      ownerKey = unit.key;
      const left = prevLiveEnd(end);
      start = left === null ? parentY._start : left.right;
    } else {
      const cs = this.state.containers.get(parentY);
      if (cs === undefined || cs.kind !== 'i') {
        // The line it was in is gone, and a block node follows: the end of
        // the nearest line before it in its container, else the start of
        // the nearest one after, never a point in another block's
        // structure. (A live position next to a block node keeps the
        // selection as it is.)
        return found.deleted ? this.$nearestLinePoint(item) : null;
      }
      ownerKey = cs.key;
      start = parentY._start;
    }
    let offset = 0;
    for (let it = start; it !== null && it !== item; it = it.right) {
      offset += shownLength(it, hidden);
    }
    offset +=
      item === end
        ? 0
        : hidden === null
          ? diff
          : hidden.shownBefore(item, diff);
    const owner = $getNodeByKey(ownerKey);
    if (!$isElementNode(owner)) {
      return null;
    }
    return $pointAtAtom(owner, offset);
  }
}

function $lineEndPoint(
  line: LexicalNode,
  atEnd: boolean,
): {key: NodeKey; offset: number; type: 'text' | 'element'} | null {
  if (!$isElementNode(line)) {
    return null;
  }
  const text = atEnd ? line.getLastDescendant() : line.getFirstDescendant();
  if ($isTextNode(text)) {
    return {
      key: text.getKey(),
      offset: atEnd ? text.getTextContentSize() : 0,
      type: 'text',
    };
  }
  return {
    key: line.getKey(),
    offset: atEnd ? line.getChildrenSize() : 0,
    type: 'element',
  };
}

function $atomSize(node: LexicalNode): number {
  if ($isTextNode(node)) {
    return node.getTextContentSize();
  }
  if ($isWrapper(node)) {
    return (node as ElementNode)
      .getChildren()
      .reduce((n, c) => n + $atomSize(c), 0);
  }
  return 1;
}

/**
 * Keep the selection's points inside their nodes after a remote read. A
 * selection of another kind (a table's cells, a node selection) that names a
 * node the read removed is dropped: Lexical keeps it as it is, and every
 * reader of the selection (a table's own selection handler) would throw.
 */
const NO_TRANSFORMS: ReadonlySet<Transform<LexicalNode>> = new Set();

/** The keys of an element's subtree, in order (see $refreshGroups). */
function $shapeOf(node: ElementNode): string {
  let out = '';
  const walk = (n: ElementNode) => {
    for (let c = n.getFirstChild(); c !== null; c = c.getNextSibling()) {
      out += c.getKey() + ',';
      if ($isElementNode(c)) {
        out += '(';
        walk(c);
        out += ')';
      }
    }
  };
  walk(node);
  return out;
}

function $clampSelection(): void {
  const selection = $getSelection();
  if (selection === null) {
    return;
  }
  if (!$isRangeSelection(selection)) {
    const {anchor, focus} = selection as {
      anchor?: PointType;
      focus?: PointType;
    };
    let lost = false;
    try {
      for (const point of [anchor, focus]) {
        if (point !== undefined) {
          const node = $getNodeByKey(point.key);
          lost = lost || node === null || !node.isAttached();
        }
      }
      lost = lost || selection.getNodes().some(node => !node.isAttached());
    } catch (_error) {
      // A selection whose nodes cannot be found.
      lost = true;
    }
    if (lost) {
      $setSelection(null);
    }
    return;
  }
  for (const point of [selection.anchor, selection.focus]) {
    const node = $getNodeByKey(point.key);
    if (node === null || !node.isAttached()) {
      $setSelection(null);
      return;
    }
    const size = $isTextNode(node)
      ? node.getTextContentSize()
      : $isElementNode(node)
        ? node.getChildrenSize()
        : 0;
    if (point.offset > size) {
      point.set(point.key, size, point.type);
    }
  }
}

/** The line or inline container whose content holds `node`. */
function $ownerOf(node: LexicalNode): ElementNode | null {
  let parent = node.getParent();
  while (parent !== null && $isWrapper(parent)) {
    parent = parent.getParent();
  }
  return parent;
}

function $atomsBefore(owner: ElementNode, target: LexicalNode): number {
  let n = 0;
  const visit = (el: ElementNode): boolean => {
    for (const c of el.getChildren()) {
      if (c.is(target)) {
        return true;
      }
      if ($isWrapper(c)) {
        if (visit(c as ElementNode)) {
          return true;
        }
      } else {
        n += $atomSize(c);
      }
    }
    return false;
  };
  visit(owner);
  return n;
}

function $pointAtAtom(
  owner: ElementNode,
  offset: number,
): {key: NodeKey; offset: number; type: 'text' | 'element'} {
  let remaining = offset;
  let lastText = null as LexicalNode | null;
  const visit = (
    el: ElementNode,
  ): {key: NodeKey; offset: number; type: 'text' | 'element'} | null => {
    const children = el.getChildren();
    for (let i = 0; i < children.length; i++) {
      const c = children[i];
      if ($isWrapper(c)) {
        const r = visit(c as ElementNode);
        if (r !== null) {
          return r;
        }
        continue;
      }
      const size = $atomSize(c);
      if ($isTextNode(c)) {
        lastText = c;
        if (remaining <= size) {
          return {key: c.getKey(), offset: remaining, type: 'text'};
        }
      } else if (remaining === 0) {
        return {key: el.getKey(), offset: i, type: 'element'};
      }
      remaining -= size;
    }
    return null;
  };
  const found = visit(owner);
  if (found !== null) {
    return found;
  }
  if (lastText !== null) {
    const t = lastText as LexicalNode;
    return {key: t.getKey(), offset: $atomSize(t), type: 'text'};
  }
  return {
    key: owner.getKey(),
    offset: owner.getChildrenSize(),
    type: 'element',
  };
}

/**
 * The nodes of a state set whole: `setEditorState` with a state the editor
 * did not parse marks only the root dirty, while its nodes replace the
 * previous ones. Every node that differs from the previous state is then
 * part of the change (an ordinary update marks every node it writes
 * dirty), however deep: a descendant differs while its ancestors stay the
 * same objects when a state saved earlier is set again. Returns the dirty
 * elements and leaves with those nodes added, or null when the commit
 * changed nothing it did not mark dirty.
 */
function $replacedNodes(
  dirtyElements: Map<NodeKey, boolean>,
  dirtyLeaves: Set<NodeKey>,
  prevEditorState: EditorState,
  editorState: EditorState,
): [Map<NodeKey, boolean>, Set<NodeKey>] | null {
  const prevMap = prevEditorState._nodeMap;
  const nodeMap = editorState._nodeMap;
  const root = nodeMap.get('root');
  // Nearly every ordinary edit marks a text node dirty, and a state set
  // whole marks only the root (unless it holds another root): the scan,
  // which is as long as the document, runs for those alone.
  if (
    root === undefined ||
    (dirtyLeaves.size > 0 && root === prevMap.get('root'))
  ) {
    return null;
  }
  let elements: Map<NodeKey, boolean> | null = null;
  let leaves: Set<NodeKey> | null = null;
  for (const [key, node] of nodeMap) {
    if (
      prevMap.get(key) !== node &&
      !dirtyElements.has(key) &&
      !dirtyLeaves.has(key)
    ) {
      if (elements === null || leaves === null) {
        elements = new Map(dirtyElements);
        leaves = new Set(dirtyLeaves);
      }
      if ($isElementNode(node)) {
        elements.set(key, true);
      } else {
        leaves.add(key);
      }
    }
  }
  return elements === null || leaves === null ? null : [elements, leaves];
}

/**
 * A client id derived from content (the initial content's, see
 * YBinding#seedUpdate): a hash of
 * `seed` in the document's client id range (see {@link ClientIDRange}), 53
 * bits under `'uint53'` (Yjs 14's own range) and 32 bits under `'uint32'`.
 * Equal seeds give equal ids, so clients writing the same items from the
 * same inputs write them once. Different seeds share an id only with the
 * probability of a collision in that range (a shared id with different items
 * would diverge), the same odds as two random client ids. Every client of a
 * document must therefore use the same range.
 */
function initClientID(seed: string, range: ClientIDRange = 'uint53'): number {
  // cyrb53 (public domain).
  let h1 = 0xdeadbeef;
  let h2 = 0x41c6ce57;
  for (let i = 0; i < seed.length; i++) {
    const ch = seed.charCodeAt(i);
    h1 = Math.imul(h1 ^ ch, 2654435761);
    h2 = Math.imul(h2 ^ ch, 1597334677);
  }
  h1 = Math.imul(h1 ^ (h1 >>> 16), 2246822507);
  h1 ^= Math.imul(h2 ^ (h2 >>> 13), 3266489909);
  h2 = Math.imul(h2 ^ (h2 >>> 16), 2246822507);
  h2 ^= Math.imul(h1 ^ (h1 >>> 13), 3266489909);
  const id =
    range === 'uint53'
      ? 0x100000000 * (h2 & 0x1fffff) + (h1 >>> 0)
      : (h1 ^ h2) >>> 0;
  return id === 0 ? 1 : id;
}

/**
 * Containers of up to this many units (lines and nodes) get the
 * whole-container self-check after every structural change; bigger ones are
 * sampled (see YBindingOptions.selfCheck).
 */
const SELF_CHECK_FULL_UNITS = 256;

function sampleWholeContainer(cs: CS): boolean {
  const n = cs.units.length;
  return (
    n <= SELF_CHECK_FULL_UNITS || Math.random() < SELF_CHECK_FULL_UNITS / n
  );
}

/**
 * Undo must not delete a container a peer has put content in (its content
 * would go with it): a container holding live content of a client other
 * than the one that created it. The clients of each subtree are computed
 * once per undo (`cache`).
 */
function isNonEmptyContainer(
  item: Item,
  cache: WeakMap<YNode, Set<number>>,
): boolean {
  if (!(item.content instanceof ContentType)) {
    return false;
  }
  const name = nameOf(item);
  if (name === MARKER || name === RUN_END) {
    return false;
  }
  const clientsOf = (type: YNode): Set<number> => {
    let clients = cache.get(type);
    if (clients === undefined) {
      clients = new Set();
      for (let it = type._start; it !== null; it = it.right) {
        if (it.deleted) {
          continue;
        }
        if (it.countable) {
          clients.add(it.id.client);
        }
        if (it.content instanceof ContentType) {
          for (const c of clientsOf(it.content.type)) {
            clients.add(c);
          }
        }
      }
      // Its named slots (see Slots.ts) are its content too.
      for (const it of type._map.values()) {
        if (!it.deleted && it.content instanceof ContentType) {
          clients.add(it.id.client);
          for (const c of clientsOf(it.content.type)) {
            clients.add(c);
          }
        }
      }
      cache.set(type, clients);
    }
    return clients;
  };
  for (const c of clientsOf(item.content.type)) {
    if (c !== item.id.client) {
      return true;
    }
  }
  return false;
}

/**
 * Keep local groups in the shape readers rebuild: adjacent top-level groups
 * with equal key fields are one group.
 */
function $canonicalizeGroup(
  node: ElementNode,
  isIdentified: ((block: LexicalNode) => boolean) | null,
): void {
  const spec = getGroupSpec(klassOf(node));
  if (spec === null || !node.isAttached()) {
    return;
  }
  // A group without items has no shared representation (its items carry
  // it): remove it, with a nested-level wrapper it leaves empty.
  if (node.getChildrenSize() === 0) {
    const parent = node.getParent();
    node.remove();
    if (
      parent !== null &&
      parent.getChildrenSize() === 0 &&
      spec.items.includes(klassOf(parent)) &&
      parent.getParent() !== null &&
      getGroupSpec(klassOf(parent.getParent()!)) === spec
    ) {
      parent.remove();
    }
    return;
  }
  // Each group level owns its state: a group that is not an identified
  // block (a nested list) keeps no block id, nor one a group it is inside
  // holds (see $withoutOuterId).
  const id = $getState(node, blockIdState);
  if (typeof id === 'string' && isIdentified !== null && !isIdentified(node)) {
    $setBlockId(node, undefined);
  } else if (typeof id === 'string') {
    for (
      let w = node.getParent(), g = w === null ? null : w.getParent();
      w !== null &&
      g !== null &&
      spec.items.includes(klassOf(w)) &&
      getGroupSpec(klassOf(g)) === spec;
      w = g.getParent(), g = w === null ? null : w.getParent()
    ) {
      if ($getState(g, blockIdState) === id) {
        $setBlockId(node, undefined);
        break;
      }
    }
  }
  // The first declared key field only (see the reader's grouping).
  const sameKey = (a: ElementNode, b: ElementNode) => {
    if (klassOf(a) !== klassOf(b)) {
      return false;
    }
    const fa = $groupFields(a, spec);
    const fb = $groupFields(b, spec);
    return spec.key.every(
      f => stableStringify(fa[f] ?? null) === stableStringify(fb[f] ?? null),
    );
  };
  // Its own items: two adjacent wrapper items each holding an equal group
  // read back as one wrapper (an item between them was moved away).
  const nestedIn = (w: LexicalNode | null): ElementNode | null => {
    if (
      !$isElementNode(w) ||
      w.getChildrenSize() !== 1 ||
      !spec.items.includes(klassOf(w))
    ) {
      return null;
    }
    const g = w.getFirstChild();
    return $isElementNode(g) && getGroupSpec(klassOf(g)) === spec ? g : null;
  };
  for (let child = node.getFirstChild(); child !== null; ) {
    const next = child.getNextSibling();
    const a = nestedIn(child);
    const b = nestedIn(next);
    if (a !== null && b !== null && sameKey(a, b)) {
      $appendMerging(a, b, sameKey);
      next!.remove();
      continue;
    }
    child = next;
  }
  // Nested levels: two adjacent wrapper items each holding an equal group
  // read back as one wrapper.
  const wrapper = node.getParent();
  if (
    wrapper !== null &&
    wrapper.getChildrenSize() === 1 &&
    spec.items.includes(klassOf(wrapper))
  ) {
    const nestedOf = (w: LexicalNode | null): ElementNode | null => {
      if (!$isElementNode(w) || w.getChildrenSize() !== 1) {
        return null;
      }
      const g = w.getFirstChild();
      return $isElementNode(g) && klassOf(g) === klassOf(node) ? g : null;
    };
    const before = nestedOf(wrapper.getPreviousSibling());
    if (before !== null && sameKey(before, node)) {
      $appendMerging(before, node, sameKey);
      wrapper.remove();
      return;
    }
    const after = nestedOf(wrapper.getNextSibling());
    if (after !== null && sameKey(node, after)) {
      const afterWrapper = after.getParent()!;
      $appendMerging(node, after, sameKey);
      afterWrapper.remove();
    }
  }
  const prev = node.getPreviousSibling();
  if (
    $isElementNode(prev) &&
    getGroupSpec(klassOf(prev)) !== null &&
    sameKey(prev, node)
  ) {
    $appendMerging(prev, node, sameKey);
    node.remove();
    return;
  }
  const next = node.getNextSibling();
  if (
    $isElementNode(next) &&
    getGroupSpec(klassOf(next)) !== null &&
    sameKey(node, next)
  ) {
    $appendMerging(node, next, sameKey);
    next.remove();
  }
}

/**
 * Move the children of `source` to the end of `target`. Where the two
 * meet, two wrapper items each holding an equal nested group are merged
 * too (recursively), as a reader builds them: consecutive deeper items share
 * one wrapper.
 */
function $appendMerging(
  target: ElementNode,
  source: ElementNode,
  sameKey: (a: ElementNode, b: ElementNode) => boolean,
): void {
  const last = target.getLastChild();
  const children = source.getChildren();
  $appendAll(target, children);
  const first = children[0];
  const nestedOf = (w: LexicalNode | null | undefined): ElementNode | null => {
    if (!$isElementNode(w) || w.getChildrenSize() !== 1) {
      return null;
    }
    const g = w.getFirstChild();
    return $isElementNode(g) && getGroupSpec(klassOf(g)) !== null ? g : null;
  };
  const a = nestedOf(last);
  const b = nestedOf(first);
  if (a !== null && b !== null && sameKey(a, b)) {
    $appendMerging(a, b, sameKey);
    first!.remove();
  }
}

/**
 * What a cursor (see YBinding#$captureCursor) leaves out of a selection: a
 * range's typing format and style (a caret where bold was toggled), or the
 * nodes a node selection holds (a selected block decorator), by their paths
 * from the root. Kept by the read-back of initialization, which shows the
 * editor's own content as stored, in the same shape (see initializeInner).
 */
type SelectionState =
  | {kind: 'range'; format: number; style: string}
  | {kind: 'node'; nodes: {path: number[]; type: string}[]};

function $selectionState(): SelectionState | null {
  const selection = $getSelection();
  if ($isRangeSelection(selection)) {
    return {format: selection.format, kind: 'range', style: selection.style};
  }
  if ($isNodeSelection(selection)) {
    const nodes: {path: number[]; type: string}[] = [];
    for (const node of selection.getNodes()) {
      const path: number[] = [];
      let n: LexicalNode = node;
      for (let p = n.getParent(); p !== null; p = n.getParent()) {
        path.push(n.getIndexWithinParent());
        n = p;
      }
      if ($isRootNode(n)) {
        nodes.push({path: path.reverse(), type: node.getType()});
      }
    }
    return {kind: 'node', nodes};
  }
  return null;
}

function $restoreSelectionState(kept: SelectionState): void {
  if (kept.kind === 'range') {
    const selection = $getSelection();
    if ($isRangeSelection(selection)) {
      selection.format = kept.format;
      selection.style = kept.style;
    }
    return;
  }
  const selection = $createNodeSelection();
  for (const {path, type} of kept.nodes) {
    let node: LexicalNode | null = $getRoot();
    for (const i of path) {
      node = $isElementNode(node) ? node.getChildAtIndex(i) : null;
    }
    if (node !== null && node.getType() === type) {
      selection.add(node.getKey());
    }
  }
  if (selection.getNodes().length > 0) {
    $setSelection(selection);
  }
}

/**
 * The microtask that ends a task for commitsAtOnce, made outside the binding
 * so that it keeps only `task`: a closure made in the update listener would
 * keep the binding (and the payload), so a binding disposed in the same task
 * (a headless call) would be kept, with its document, until the caller
 * yields.
 */
function endOfTask(task: {committed: boolean}): () => void {
  return () => {
    task.committed = false;
  };
}

/**
 * Split a text node holding line feeds into text and line break nodes, as
 * the document stores and every reader shows it (see YBinding#startInner),
 * whatever its mode or class. The parts are Lexical's splitText's: each
 * keeps the node's format, style and NodeState; the first is the node
 * itself (its class and mode, but a segmented node's is a new normal text
 * node), the others are normal text nodes. The author writes them so, and
 * every reader shows them so. Each line break gets the NodeState its line
 * feed had (a comment on just the line feed stays on it).
 */
function $splitLineBreaks(node: TextNode): void {
  const text = node.getTextContent();
  if (!text.includes('\n')) {
    return;
  }
  const offsets: number[] = [];
  for (let i = text.indexOf('\n'); i >= 0; i = text.indexOf('\n', i + 1)) {
    offsets.push(i, i + 1);
  }
  // splitText takes its offsets as arguments, which are bounded in number
  // (see Arrays.ts): split in pieces, from the end, so that each piece's
  // offsets fall in the first part the previous piece left (the node
  // itself, or the normal text node that replaces a segmented one).
  let head = node;
  for (let end = offsets.length; end > 0; end -= ARGUMENTS_CHUNK) {
    const parts = head.splitText(
      ...offsets.slice(Math.max(0, end - ARGUMENTS_CHUNK), end),
    );
    head = parts[0];
    // The first part is split again by the next piece, if any.
    for (let i = end > ARGUMENTS_CHUNK ? 1 : 0; i < parts.length; i++) {
      const part = parts[i];
      if (part.getTextContent() === '\n') {
        const br = $createLineBreakNode();
        const st = (part.exportJSON() as {$?: Record<string, unknown>}).$;
        if (st !== undefined) {
          br.updateFromJSON({$: st} as Parameters<
            LineBreakNode['updateFromJSON']
          >[0]);
        }
        part.replace(br);
      }
    }
  }
}
