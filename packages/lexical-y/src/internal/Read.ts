/**
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 */

import {blockIdState} from '@lexical/extension';
import {
  ContentFormat,
  ContentString,
  ContentType,
  createID,
  Item,
  type Node as YNode,
} from '@y/y';
import {
  $createLineBreakNode,
  $createParagraphNode,
  $getNodeByKey,
  $getSelection,
  $getState,
  $getWritableNodeState,
  $isElementNode,
  $isLineBreakNode,
  $isParagraphNode,
  $isRangeSelection,
  $isRootNode,
  $isTextNode,
  $parseSerializedNode,
  $setSelection,
  type ElementNode,
  type Klass,
  type LexicalNode,
  NODE_STATE_DIRECT,
  type NodeKey,
  type SerializedLexicalNode,
  type TextNode,
} from 'lexical';

import {$appendAll, pushAll, spliceAll} from './Arrays';
import {type Formats} from './Cursor';
import {type MovePlan, moveReadStats, planMoveRead} from './MoveRead';
import {
  enterZone,
  formatsAfterItem,
  isMoveItem,
  type Rec,
  stepZone,
  type Zone,
  Zones,
  ZoneView,
} from './Moves';
import {
  $groupFields,
  $levelItemFields,
  $lineAttrs,
  $lineBreakAttrs,
  $nodeAttrs,
  $schemaJSON,
  $setTextFields,
  $textAttrs,
  $wrapperAttrs,
  type Attrs,
  decodeFormatValue,
  FIELD_PREFIX,
  getContainerGroupSpec,
  getGroupSpec,
  getLineSpec,
  getWrapperSpec,
  GROUP_FIELD_PREFIX,
  GROUP_KEY,
  type GroupSpec,
  INLINE_PREFIX,
  isBlockNodeType,
  isUnsafeKey,
  joinSetMembers,
  joinSetMembersInJSON,
  KIND_KEY,
  klassOf,
  LEVEL_KEY,
  lineBreakStateFromAttrs,
  MARKER,
  nodeJSONFromAttrs,
  OUTER_KEY,
  SEGMENT_KEY,
  stableStringify,
  STATE_PREFIX,
  textJSONFromAttrs,
  TYPE_KEY,
  WRAPPER_FIELDS_KEY,
  WRAPPER_PREFIX,
  wrappersFromAttrs,
  type WrapperValue,
} from './Schema';
import {
  $setBlockId,
  $withoutOuterId,
  groupBlockId,
  NO_IDS,
  storedTypeOf,
} from './Schema';
import {$readSlots, $replaceStored, SLOT_PREFIX} from './Slots';
import {
  type CS,
  EMPTY_FORMATS,
  isBlockNodeItem,
  isEndItem,
  type Kind,
  lineStart,
  nameOf,
  nextZoneEnd,
  physicalStarts,
  prevBoundary,
  startItemAfter,
  type State,
  typeOf,
  type Unit,
  type UnitKind,
} from './State';
import {
  groupKeySig,
  groupSig as writerGroupSig,
  longestIncreasing,
} from './Write';

export type Parsed = {
  kind: UnitKind;
  end: Item | null;
  startItem: Item | null;
  stop: Item | null;
  start: Formats;
  /** The move record whose range holds the unit's end (null: none). */
  zone: Zone;
  /** The zone a walk of the unit's content starts in (see `lineStart`). */
  startZone: Zone;
};

/** The zone a parse walks, and how to find a record's start formats. */
export type ParseZone = {
  zones: Zones;
  zone: Zone;
  startOf: (rec: Rec) => Formats;
  /** Formats right after `it` (a record's start or a record). */
  formatsAfter: (it: Item) => Formats;
};

type Piece =
  | {
      kind: 'text';
      text: string;
      tattrs: Attrs;
      tsig: string;
      wrappers: WrapperValue[];
      /** This text is the node being composed (see $readInline). */
      composed?: boolean;
    }
  | {kind: 'br'; tattrs: Attrs; wrappers: WrapperValue[]}
  | {kind: 'node'; y: YNode; wrappers: WrapperValue[]};

type GroupItem = {
  node: ElementNode;
  /**
   * The id a group whose first item this is gets when its items store none
   * (see derivedBlockId), or null.
   */
  derivedId: string | null;
  level: number;
  gtype: string;
  gkey: Attrs;
  gsig: string;
  spec: GroupSpec;
  /** The group key at each level 0..level (null: not recorded). */
  keys: (Attrs | null)[];
  /** The fields of the wrapper item at each outer level (null: none). */
  wrappers: (Attrs | null)[];
};

type Pool = {
  groups: Map<string, ElementNode[]>;
  levels: ElementNode[];
  /** The keys of the wrappers in `levels` not taken yet. */
  levelKeys: Set<NodeKey>;
  /** Nodes that are lines of this read: never reused as wrappers. */
  lines: Set<NodeKey>;
};

/**
 * Parse the units of a block container between two items. With moves, only
 * the units of one zone are parsed (other zones' content is skipped, formats
 * stay positional), and an active move record is replaced by the units of
 * its range.
 */
export function parseRange(
  start: Item | null,
  stop: Item | null,
  formats: Formats,
  pz: ParseZone | null = null,
  last: Item | null = null,
): {parsed: Parsed[]; after: Formats} {
  const parsed: Parsed[] = [];
  const current = new Map(formats);
  // Units share a copy of `current` until a format item changes it (start
  // formats are never changed in place).
  let snap: Formats | null = null;
  const snapshot = (): Formats => {
    if (snap === null) {
      snap = current.size > 0 ? new Map(current) : EMPTY_FORMATS;
    }
    return snap;
  };
  const zone = pz === null ? null : pz.zone;
  let unitStart = start;
  let unitFormats = snapshot();
  let pending = false;
  // Move records seen since the last unit: their units show before the unit
  // the records are in (a record is not a boundary of the text around it,
  // so text typed next to it concurrently stays in its line).
  let records: Item[] = [];
  // Records after text that no marker ends (before a block node, or at the
  // end): they show after that text (the writer puts a record right after
  // such text to show it there).
  let after: Item[] = [];
  const flushRecords = (list: Item[] = records) => {
    if (list.length === 0 || pz === null) {
      return;
    }
    for (const it of list) {
      const rec = pz.zones.rec(it);
      if (rec === undefined) {
        continue;
      }
      const sub = parseRange(
        rec.s === null ? (it.parent as YNode)._start : rec.s.right,
        rec.e.right,
        pz.startOf(rec),
        {...pz, zone: it},
        rec.e,
      );
      for (const p of sub.parsed) {
        parsed.push(p);
      }
    }
  };
  // With moves, the walk enters the ranges that inline records of the zone
  // show in their place (a line can continue there).
  const walk = pz === null ? null : new ZoneView(pz.zones, pz.zone, null);
  const y = start === null ? null : (start.parent as YNode);
  let unitZone: Zone = zone;
  let startPending = false;
  let prev: Item | null = null;
  for (
    let it =
      start === stop
        ? null
        : walk === null
          ? start
          : enterZone(walk, y!, start, stop);
    it !== null && (walk !== null || it !== stop);
    prev = it,
      it =
        walk === null
          ? it === last
            ? null
            : it.right
          : stepZone(
              walk,
              y!,
              it,
              last === null ? stop : null,
              last,
              last === null ? undefined : zone,
            )
  ) {
    const wz = walk === null ? null : walk.zone;
    if (walk !== null && (prev === null ? it !== start : it !== prev.right)) {
      // A jump into or out of an inline range: positional formats.
      const f = it.left === null ? EMPTY_FORMATS : pz!.formatsAfter(it.left);
      current.clear();
      f.forEach((v, k) => current.set(k, v));
      snap = null;
    }
    if (
      startPending &&
      // A unit starts at its zone's first item after the previous end: the
      // walk can pass other zones' items first (an item of an inline range
      // it shows later, which can be the item that ends the unit).
      (it.deleted || pz!.zones.ownerOf(it) === wz || isMoveItem(it))
    ) {
      unitStart = it;
      unitZone = wz;
      unitFormats = new Map(current);
      startPending = false;
    } else if (prev === null) {
      unitStart = it;
      unitZone = wz;
      unitFormats = new Map(current);
    }
    if (it.deleted) {
      continue;
    }
    const content = it.content;
    if (content instanceof ContentFormat) {
      if (content.value === null) {
        current.delete(content.key);
      } else {
        current.set(content.key, content.value);
      }
      snap = null;
      continue;
    }
    if (!it.countable) {
      continue;
    }
    if (pz !== null && pz.zones.ownerOf(it) !== wz) {
      continue;
    }
    if (isMoveItem(it)) {
      (pending ? after : records).push(it);
      continue;
    }
    if (isEndItem(it)) {
      if (isBlockNodeItem(it)) {
        flushRecords();
        if (pending) {
          parsed.push({
            end: null,
            kind: 'implicit',
            start: unitFormats,
            startItem: unitStart,
            startZone: unitZone,
            stop: it,
            // Text no marker ends belongs to the zone its walk starts in
            // (it can run into an inline range shown in its line).
            zone: unitZone,
          });
        }
        flushRecords(after);
        records = [];
        after = [];
        parsed.push({
          end: it,
          kind: 'node',
          start: unitFormats,
          startItem: it,
          startZone: wz,
          stop: it.right,
          zone: wz,
        });
      } else {
        flushRecords();
        flushRecords(after);
        records = [];
        after = [];
        parsed.push({
          end: it,
          kind: nameOf(it) === MARKER ? 'line' : 'run',
          start: unitFormats,
          startItem: unitStart,
          startZone: unitZone,
          stop: it,
          zone: wz,
        });
      }
      unitStart = it.right;
      unitZone = wz;
      unitFormats = new Map(current);
      startPending = walk !== null;
      pending = false;
    } else {
      pending = true;
    }
  }
  flushRecords();
  if (pending) {
    parsed.push({
      end: null,
      kind: 'implicit',
      start: unitFormats,
      startItem: unitStart,
      startZone: unitZone,
      stop,
      zone: walk === null ? zone : unitZone,
    });
  }
  flushRecords(after);
  return {after: current, parsed};
}

export class Reader {
  private readonly isKnownWrapper: (type: string) => boolean;
  /** Item -> unit cache for one read. */
  private located = new Map<Item, Unit | null>();
  /** Inline ranges whose showing line one read already read again. */
  private inlineReads = new Set<Rec>();
  /** Formats in effect after the content last read by $pieces. */
  private lastFormats: Formats = EMPTY_FORMATS;
  readonly fresh = new Set<YNode>();
  /** Nesting of entry points (see $settleIds, run by the outermost). */
  private depth = 0;
  /**
   * The line or inline container the local editor is composing in (set by
   * the binding). Remote inserts into it are not read (see Hidden): they
   * are collected in `deferred`. `composingRead` tells that its content was
   * read anyway (a structural or attribute change), so it shows everything.
   * A read that only moves the line (a region read pulls it in to regroup
   * its list) keeps its content, and what is hidden stays hidden.
   */
  composingKey: NodeKey | null = null;
  readonly deferred: Item[] = [];
  composingRead = false;
  /** Units whose marker attributes changed in this transaction. */
  private readonly attrChanged = new Set<Unit>();
  /** Containers whose structure this read rebuilt (for the self-check). */
  readonly rebuilt = new Set<CS>();
  /**
   * Nodes this read placed inside a line (a block decorator written into a
   * paragraph without the normalization) that store no block id: they get
   * the id derived from their item once in place, if identified blocks (see
   * $settleIds), as nodes stored in a container do (see $commitUnits).
   */
  private readonly inlineStored = new Set<NodeKey>();
  constructor(readonly state: State) {
    const nodes = state.editor._nodes;
    this.isKnownWrapper = type => {
      const info = nodes.get(type);
      return info !== undefined && getWrapperSpec(info.klass) !== null;
    };
  }

  // -------------------------------------------------------------------------
  // Moves

  /** How to parse the native zone of `cs` (null: it holds no moves). */
  /**
   * Whether the units of `cs` show what a read of its shared content shows
   * (after a write with move records: deleting a record can make another
   * one show, or show elsewhere, where the editor did not change).
   */
  matchesShared(cs: CS): boolean {
    if (cs.kind !== 'b' || (cs.y._item !== null && cs.y._item.deleted)) {
      return true;
    }
    const {parsed} = parseRange(cs.y._start, null, EMPTY_FORMATS, this.pz(cs));
    if (parsed.length !== cs.units.length) {
      return false;
    }
    for (let k = 0; k < parsed.length; k++) {
      const p = parsed[k];
      const u = cs.units[k];
      if (
        p.end !== u.end ||
        (p.zone ?? null) !== (u.zone ?? null) ||
        p.kind !== u.kind
      ) {
        return false;
      }
    }
    return true;
  }

  private pz(cs: CS): ParseZone | null {
    const zones = this.state.zonesOf(cs.y);
    if (zones === null) {
      return null;
    }
    // The formats in effect after each active record's start and after
    // each record (where walks jump), from one walk of the container
    // (formats are positional).
    let table: Map<Item, Formats> | null = null;
    const formatsAfter = (item: Item): Formats => {
      if (table === null) {
        table = new Map();
        const wanted = new Set<Item>();
        for (const r of zones.active) {
          if (r.s !== null) {
            wanted.add(r.s);
          }
          wanted.add(r.item);
        }
        const formats = new Map<string, unknown>();
        for (
          let it = cs.y._start;
          it !== null && wanted.size > table.size;
          it = it.right
        ) {
          if (!it.deleted && it.content instanceof ContentFormat) {
            const {key, value} = it.content;
            if (value === null) {
              formats.delete(key);
            } else {
              formats.set(key, value);
            }
          }
          if (wanted.has(it)) {
            table.set(it, new Map(formats));
          }
        }
      }
      return table.get(item) ?? formatsAfterItem(cs.y, item);
    };
    return {
      formatsAfter,
      startOf: rec => (rec.s === null ? EMPTY_FORMATS : formatsAfter(rec.s)),
      zone: null,
      zones,
    };
  }

  /** The view of a unit's zone (null: its container holds no moves). */
  private zv(cs: CS, zone: Zone | undefined): ZoneView | null {
    const zones = this.state.zonesOf(cs.y);
    return zones === null ? null : new ZoneView(zones, zone ?? null, null);
  }

  // -------------------------------------------------------------------------
  // Entry points

  /** Read a whole container into its Lexical node. */
  $readFull(
    cs: CS,
    el: ElementNode,
    affected: ReadonlySet<Unit> | null = null,
  ): void {
    this.depth++;
    try {
      this.$readFullInner(cs, el, affected);
    } finally {
      if (--this.depth === 0) {
        this.$settleIds();
      }
    }
  }

  private $readFullInner(
    cs: CS,
    el: ElementNode,
    affected: ReadonlySet<Unit> | null,
  ): void {
    if (cs.kind === 'b' && !this.state.hasMoves(cs.y) && holdsMove(cs.y)) {
      this.state.noteMoves(cs.y);
    }
    this.fresh.add(cs.y);
    this.rebuilt.add(cs);
    if (
      this.composingKey !== null &&
      (cs.key === this.composingKey ||
        cs.units.some(u => u.key === this.composingKey))
    ) {
      this.composingRead = true;
    }
    if (cs.kind === 'i') {
      this.$setChildren(
        el,
        this.$readInline(cs.y._start, null, EMPTY_FORMATS, el),
      );
      for (const u of cs.units) {
        this.state.dropUnit(u);
      }
      cs.units = [];
      return;
    }
    const {parsed} = parseRange(cs.y._start, null, EMPTY_FORMATS, this.pz(cs));
    const old = cs.units;
    const {units, tops} = this.$materialize(cs, el, parsed, old, affected);
    this.$setChildren(el, tops);
    this.$commitUnits(cs, 0, old.length, units, old);
  }

  /** Apply a remote transaction's changes. */
  $apply(
    childItems: Map<YNode, Item[]>,
    attrKeys: Map<YNode, Set<string>>,
  ): void {
    this.depth++;
    try {
      this.$applyInner(childItems, attrKeys);
    } finally {
      if (--this.depth === 0) {
        this.$settleIds();
      }
    }
  }

  /**
   * Blocks that store the same id (concurrent edits split a list whose items
   * all store its id, or copied a block's marker), and blocks that store
   * another block's derived id (a block's JSON copied with the id a reader
   * showed): every block shows the first id of its own list that no block
   * before it in document order shows (see $shownId), its stored id, then
   * the id derived from its own Yjs identity (see derivedBlockId), then
   * that id followed by `_d`s. Every reader shows the same, no two blocks
   * show one id, BlockIdExtension has nothing to name, and the next write of
   * such a block stores the id it shows.
   */
  private $settleIds(): void {
    const state = this.state;
    const isIdentified = state.blockIds;
    if (isIdentified === null) {
      state.touchedIds.clear();
      this.inlineStored.clear();
      return;
    }
    for (const key of this.inlineStored) {
      const node = $getNodeByKey(key);
      const y = state.yByKey.get(key);
      if (
        node !== null &&
        node.isAttached() &&
        y !== undefined &&
        y._item !== null &&
        y.getAttr(STATE_PREFIX + blockIdState.key) === undefined
      ) {
        const want = isIdentified(node)
          ? storedDerivedId(node, y._item)
          : undefined;
        if ($getState(node, blockIdState) !== want) {
          $setBlockId(node, want);
        }
        this.noteDerived(want ?? null);
      }
    }
    this.inlineStored.clear();
    $touchChanged(state);
    const pass = newSettlePass();
    // Only the ids whose claimants this update changed: settling costs what
    // the change touched, however many ids the document repeats.
    const ids = new Set(state.touchedIds);
    state.touchedIds.clear();
    // A group's or wrapper item's derived id comes from its first line: a
    // group whose children changed in this read, and the blocks it is the
    // first block of, derive theirs again (or, storing one, are settled).
    const seen = new Set<NodeKey>();
    for (const key of state.refresh) {
      let n: LexicalNode | null = $getNodeByKey(key);
      while (
        $isElementNode(n) &&
        !$isRootNode(n) &&
        n.isAttached() &&
        !seen.has(n.getKey())
      ) {
        seen.add(n.getKey());
        const now = $storedIdNow(state, n);
        const stored =
          state.storedIdOf.get(n.getKey()) ??
          (typeof now === 'string' ? now : undefined);
        if (stored !== undefined) {
          ids.add(stored);
        } else if (
          !state.unitByKey.has(n.getKey()) &&
          isIdentified(n) &&
          !$inNamedSlot(n)
        ) {
          const want = this.$shownId(n, pass);
          const had = $getState(n, blockIdState);
          if (want !== null && had !== want) {
            $setBlockId(n, want);
            if (typeof had === 'string') {
              // Blocks that claim the id it showed may show it now.
              ids.add(had);
            }
          }
          const derived = this.$derivedIdOf(n);
          if (derived !== null) {
            ids.add(derived);
          }
        }
        const parent: ElementNode | null = n.getParent();
        if (
          parent === null ||
          state.csByKey.has(parent.getKey()) ||
          parent.getFirstChild() === null ||
          !parent.getFirstChild()!.is(n)
        ) {
          break;
        }
        n = parent;
      }
    }
    this.$forEachSettled(ids, pass, (node, want) => {
      if ($getState(node, blockIdState) !== want) {
        $setBlockId(node, want);
      }
      return true;
    });
  }

  /**
   * Run `f` on every block that stores one of `ids` (or derives it, see
   * $derivingBlock) with the id it shows (see $shownId). A block that shows
   * another id than the one settled (it falls back to its derived id) has
   * that id settled too, when another block stores it; a block that showed
   * another id before has that id settled too (the blocks that claim it may
   * show it now). `f` returns whether to go on with that id's fallbacks.
   * With `touched`, the ids whose index entries settling found stale are
   * settled too.
   */
  private $forEachSettled(
    ids: Iterable<string>,
    pass: SettlePass,
    f: (node: LexicalNode, want: string, id: string) => boolean,
    touched = true,
  ): void {
    const state = this.state;
    const queue = [...ids];
    const done = new Set<string>();
    while (queue.length > 0 || (touched && state.touchedIds.size > 0)) {
      if (queue.length === 0) {
        // Ids whose index entries settling found stale (see $storers).
        for (const id of state.touchedIds) {
          queue.push(id);
        }
        state.touchedIds.clear();
        pass.claimants.clear();
        pass.shown.clear();
        done.clear();
        continue;
      }
      const id = queue.pop()!;
      if (done.has(id)) {
        continue;
      }
      done.add(id);
      for (const [node, want] of this.$settlement(id, pass)) {
        const had = $getState(node, blockIdState);
        if (
          f(node, want, id) &&
          want !== id &&
          !done.has(want) &&
          this.$storedElsewhere(want, node)
        ) {
          queue.push(want);
        }
        if (typeof had === 'string' && had !== want && !done.has(had)) {
          queue.push(had);
        }
      }
    }
  }

  /** Whether a block other than `node` may store `id`. */
  private $storedElsewhere(id: string, node: LexicalNode): boolean {
    const state = this.state;
    const set = state.holdersOf.get(id);
    if (set !== undefined && (set.size > 1 || !set.has(node.getKey()))) {
      return true;
    }
    const other = state.blockIdHolder === null ? null : state.blockIdHolder(id);
    return other !== null && other.getKey() !== node.getKey();
  }

  /**
   * A read gave a block the derived id `id`: settled with the blocks that
   * store it, if any does (a copy of the id a reader showed, read before
   * the block that derives it was).
   */
  private noteDerived(id: string | null): void {
    const state = this.state;
    if (
      id !== null &&
      (state.holdersOf.has(id) ||
        (state.blockIdHolder !== null && state.blockIdHolder(id) !== null))
    ) {
      state.touchedIds.add(id);
    }
  }

  /**
   * Settle `ids` (see $settleIds) in an update of the binding's own, after
   * a local write changed which blocks store them.
   */
  $settle(ids: Iterable<string>): void {
    for (const id of ids) {
      this.state.touchedIds.add(id);
    }
    if (this.depth === 0) {
      this.$settleIds();
    }
  }

  /**
   * The ids among `ids` (and the ids their holders fall back to) whose
   * holders do not show what $settleIds gives them (a check outside an
   * update: it changes no node).
   */
  $unsettled(ids: Iterable<string>): string[] {
    const out = new Set<string>();
    if (this.state.blockIds === null) {
      return [];
    }
    this.$forEachSettled(
      ids,
      newSettlePass(),
      (node, want, id) => {
        const had = $getState(node, blockIdState);
        if (had !== want) {
          out.add(id);
          out.add(want);
          if (typeof had === 'string') {
            out.add(had);
          }
        }
        return true;
      },
      false,
    );
    return [...out];
  }

  /** The blocks that claim `ids` (see $claimants), for the self-check. */
  $claimantsOf(ids: Iterable<string>): LexicalNode[] {
    const pass = newSettlePass();
    const out: LexicalNode[] = [];
    for (const id of ids) {
      pushAll(out, this.$claimants(id, pass));
    }
    return out;
  }

  /**
   * The blocks that store `id`, and the block that derives it, each with
   * the id it shows (see $shownId), once the index of who stores it is
   * brought up to date. An id that several blocks claim is noted as
   * repeated (see State#repeatedIds).
   */
  private $settlement(id: string, pass: SettlePass): [LexicalNode, string][] {
    const state = this.state;
    const holders = this.$claimants(id, pass);
    const set = state.holdersOf.get(id);
    if (holders.length > 1 || (set !== undefined && set.size > 1)) {
      state.repeatedIds.add(id);
    } else {
      state.repeatedIds.delete(id);
    }
    if (set !== undefined && set.size === 0) {
      state.holdersOf.delete(id);
    }
    const out: [LexicalNode, string][] = [];
    for (const node of holders) {
      const want = this.$shownId(node, pass);
      if (want !== null) {
        out.push([node, want]);
      }
    }
    return out;
  }

  /**
   * The blocks that may show `id`, in document order: those that store it,
   * and the block that derives it (see $derivingBlock).
   */
  private $claimants(id: string, pass: SettlePass): LexicalNode[] {
    let out = pass.claimants.get(id);
    if (out === undefined) {
      out = this.$storers(id);
      const derived = this.$derivingBlock(id);
      if (
        derived !== null &&
        !out.some(n => n.getKey() === derived.getKey()) &&
        this.$isSettled(derived)
      ) {
        out.push(derived);
      }
      if (out.length > 1) {
        const paths = new Map(out.map(n => [n.getKey(), $pathOf(n, pass)]));
        out.sort((a, b) =>
          comparePaths(paths.get(a.getKey())!, paths.get(b.getKey())!),
        );
      }
      pass.claimants.set(id, out);
    }
    return out;
  }

  /** Whether settling gives a block its id (else BlockIdExtension does). */
  private $isSettled(node: LexicalNode): boolean {
    return (
      node.isAttached() && !$inNamedSlot(node) && this.state.blockIds!(node)
    );
  }

  /**
   * The blocks that store `id`, from the index of who stores what (brought
   * up to date where this client rewrote a block since it was read).
   */
  private $storers(id: string): LexicalNode[] {
    const state = this.state;
    const out: LexicalNode[] = [];
    const set = state.holdersOf.get(id);
    if (set !== undefined) {
      for (const key of [...set]) {
        const node = $getNodeByKey(key);
        if (node === null) {
          // Removed (its id is settled again: see $touchChanged).
          state.noteStoredId(key, undefined);
        } else if ($storedIdNow(state, node) !== id) {
          // Rewritten since it was read (by this client's own edit).
          state.noteStoredId(key, $storedIdNow(state, node));
        } else if (this.$isSettled(node)) {
          out.push(node);
        }
      }
    }
    // A block this client's own edits gave the id (not read, so not
    // noted) holds it too.
    const other = state.blockIdHolder === null ? null : state.blockIdHolder(id);
    if (
      other !== null &&
      !(set !== undefined && set.has(other.getKey())) &&
      this.$isSettled(other) &&
      $getState(other, blockIdState) === id &&
      $storedIdNow(state, other) === id
    ) {
      state.noteStoredId(other.getKey(), id);
      out.push(other);
    }
    return out;
  }

  /**
   * The id a block shows: the first of its stored id, its derived id and
   * that id followed by `_d`s that no block before it in document order
   * shows. Each block's depends only on blocks before it, so every reader
   * computes the same, whatever order the ids are settled in.
   */
  private $shownId(node: LexicalNode, pass: SettlePass): string | null {
    const key = node.getKey();
    const known = pass.shown.get(key);
    if (known !== undefined) {
      return known;
    }
    // Not reached again for the same block: only blocks before it are.
    pass.shown.set(key, null);
    const now = $storedIdNow(this.state, node);
    const stored = typeof now === 'string' ? now : undefined;
    let want: string | null = null;
    if (stored !== undefined && !this.$shownBefore(stored, node, pass)) {
      want = stored;
    } else {
      const derived = this.$derivedIdOf(node);
      for (let v = derived; v !== null; v += '_d') {
        if (v !== stored && !this.$shownBefore(v, node, pass)) {
          want = v;
          break;
        }
      }
    }
    pass.shown.set(key, want);
    return want;
  }

  /** Whether a block before `node` in document order shows `id`. */
  private $shownBefore(
    id: string,
    node: LexicalNode,
    pass: SettlePass,
  ): boolean {
    const claimants = this.$claimants(id, pass);
    let at: number[] | null = null;
    for (const other of claimants) {
      if (other.getKey() === node.getKey()) {
        continue;
      }
      if (at === null) {
        at = $pathOf(node, pass);
      }
      if (comparePaths($pathOf(other, pass), at) >= 0) {
        break;
      }
      if (this.$shownId(other, pass) === id) {
        return true;
      }
    }
    return false;
  }

  /** The id a block derives from its Yjs identity (see derivedBlockId). */
  private $derivedIdOf(node: LexicalNode): string | null {
    const state = this.state;
    const unit = state.unitByKey.get(node.getKey());
    if (unit !== undefined && unit.key === node.getKey()) {
      return unit.end !== null
        ? derivedBlockId(unit.end)
        : unit.kind === 'implicit'
          ? implicitIdOf(unit)
          : null;
    }
    // A stored node, a list stored as a node included: from its own item,
    // which no edit of its content changes.
    const y = state.yByKey.get(node.getKey());
    if (y !== undefined) {
      return y._item === null ? null : storedDerivedId(node, y._item);
    }
    if ($isGroupNode(node)) {
      // From its first line, and its level (a list nested at the start of
      // a list shares that line).
      const end = this.$firstLineEnd(node);
      return end === null
        ? null
        : derivedBlockId(end) + groupSuffix(this.$groupsAbove(node));
    }
    // A wrapper item: from its nested group's first item, and its level
    // (wrappers nested at the start of a list share that item).
    const g = $isElementNode(node) ? node.getFirstChild() : null;
    if ($isGroupNode(g)) {
      const end = this.$firstLineEnd(g);
      return end === null
        ? null
        : derivedBlockId(end) +
            wrapperSuffix(Math.max(0, this.$groupsAbove(node) - 1));
    }
    return null;
  }

  /** The end item of the first line under a group (descending into it). */
  private $firstLineEnd(group: ElementNode): Item | null {
    for (let n: LexicalNode | null = group.getFirstChild(); n !== null; ) {
      const u = this.state.unitByKey.get(n.getKey());
      if (u !== undefined && u.end !== null) {
        return u.end;
      }
      n = $isElementNode(n) ? n.getFirstChild() : null;
    }
    return null;
  }

  /** How many groups hold `node`, inside its container. */
  private $groupsAbove(node: LexicalNode): number {
    let level = 0;
    for (let p = node.getParent(); p !== null; p = p.getParent()) {
      if ($isGroupNode(p)) {
        level++;
      }
      if ($isRootNode(p) || this.state.csByKey.has(p.getKey())) {
        break;
      }
    }
    return level;
  }

  /**
   * The block that derives `id` (see $derivedIdOf), if `id` has the form of
   * a derived id, possibly followed by `_d`s, and such a block is shown,
   * whether or not it stores an id: a block storing a copy of that id (a
   * block's JSON copied with the id a reader showed) competes with it.
   */
  private $derivingBlock(id: string): LexicalNode | null {
    const m =
      /^(y([0-9a-z]+)_([0-9a-z]+)(?:_g[0-9]*|_w[0-9]*|_l)?)(?:_d)*$/.exec(id);
    if (m === null) {
      return null;
    }
    const base = m[1];
    const state = this.state;
    const client = parseInt(m[2], 36);
    const clock = parseInt(m[3], 36);
    const store = state.doc.store;
    if (
      !Number.isSafeInteger(client) ||
      !Number.isSafeInteger(clock) ||
      store.getClock(client) <= clock
    ) {
      return null;
    }
    const item = store.getItem(createID(client, clock));
    if (!(item instanceof Item) || item.id.clock !== clock || item.deleted) {
      return null;
    }
    const unit = state.unitByEnd.get(item);
    const key =
      unit !== undefined && unit.key !== null
        ? unit.key
        : item.content instanceof ContentType
          ? state.keyByY.get(item.content.type)
          : undefined;
    if (key === undefined) {
      // A line without a marker derives its id from its first character.
      const cs = state.containers.get(item.parent as YNode);
      for (const u of cs === undefined ? [] : cs.units) {
        if (u.kind === 'implicit' && u.key !== null) {
          const n = $getNodeByKey(u.key);
          if (n !== null && this.$derivedIdOf(n) === base) {
            return n;
          }
        }
      }
      return null;
    }
    // The line or node itself, or the group or wrapper item it is the first
    // line of.
    for (
      let n: LexicalNode | null = $getNodeByKey(key);
      n !== null && !$isRootNode(n);
      n = n.getParent()
    ) {
      if (this.$derivedIdOf(n) === base) {
        return n;
      }
      if (n !== null && state.csByKey.has(n.getKey()) && n.getKey() !== key) {
        break;
      }
    }
    return null;
  }

  private $applyInner(
    childItems: Map<YNode, Item[]>,
    attrKeys: Map<YNode, Set<string>>,
  ): void {
    const state = this.state;
    this.located = new Map();
    this.inlineReads = new Set();
    const markerUnits = new Map<CS, Set<Unit>>();
    const fullReads = new Set<CS>();
    for (const [y, keys] of attrKeys) {
      if (y === state.root) {
        continue;
      }
      if (y.name === MARKER) {
        const item = y._item;
        const unit = item === null ? undefined : state.unitByEnd.get(item);
        if (unit !== undefined && !item!.deleted) {
          let set = markerUnits.get(unit.cs);
          if (set === undefined) {
            set = new Set();
            markerUnits.set(unit.cs, set);
          }
          set.add(unit);
        }
        continue;
      }
      const key = state.keyByY.get(y);
      const node = key === undefined ? null : $getNodeByKey(key);
      if (node === null || (y._item !== null && y._item.deleted)) {
        continue;
      }
      this.$applyNodeAttrs(node, y);
      if ([...keys].some(k => k.startsWith(SLOT_PREFIX))) {
        // Its named slots changed (the node may have been retyped above).
        const now = $getNodeByKey(state.keyByY.get(y) ?? key!);
        if (now !== null) {
          $readSlots(this, now, y);
        }
      }
      const cs = state.containers.get(y);
      if (cs !== undefined && keys.has(KIND_KEY)) {
        const kind: Kind = y.getAttr(KIND_KEY) === 'i' ? 'i' : 'b';
        if (kind !== cs.kind) {
          cs.kind = kind;
          fullReads.add(cs);
        }
      }
    }
    for (const cs of fullReads) {
      const el = $getNodeByKey(cs.key);
      if ($isElementNode(el)) {
        this.$readFull(cs, el);
      }
    }
    for (const [y, items] of childItems) {
      const cs = state.containers.get(y);
      if (
        cs === undefined ||
        this.fresh.has(y) ||
        fullReads.has(cs) ||
        isDeleted(y)
      ) {
        continue;
      }
      const el = $getNodeByKey(cs.key);
      if (!$isElementNode(el)) {
        continue;
      }
      if (cs.kind === 'i') {
        if (cs.key === this.composingKey && this.$defer(items)) {
          continue;
        }
        if (cs.key === this.composingKey) {
          this.composingRead = true;
        }
        this.$setChildren(
          el,
          this.$readInline(y._start, null, EMPTY_FORMATS, el),
        );
      } else {
        this.$readChanges(cs, el, items, markerUnits.get(cs));
        markerUnits.delete(cs);
      }
    }
    for (const [cs, units] of markerUnits) {
      const el = $getNodeByKey(cs.key);
      if ($isElementNode(el) && !isDeleted(cs.y)) {
        this.$readChanges(cs, el, [], units);
      }
    }
    // An element that cannot be empty is shown only while its content is
    // not (as a fresh reader builds it): a stored container whose content
    // peers emptied, or filled again, is read again where it is held. One
    // not shown for a whole update is gone from the editor (Lexical drops
    // detached nodes): filled again, it is read anew there.
    for (const y of childItems.keys()) {
      const cs = state.containers.get(y);
      const el = cs === undefined ? null : $getNodeByKey(cs.key);
      if (
        typeof y.name === 'string' &&
        y.name.startsWith(INLINE_PREFIX) &&
        cs !== undefined &&
        !isDeleted(y) &&
        (el === null ||
          ($isElementNode(el) &&
            !el.canBeEmpty() &&
            (el.getChildrenSize() === 0) === el.isAttached()))
      ) {
        this.$rereadHolder(y);
      }
    }
    this.$repairSelection();
  }

  /** Read again the line (or inline container) holding a stored node. */
  private $rereadHolder(y: YNode): void {
    const item = y._item;
    if (item === null || item.deleted) {
      return;
    }
    const parent = item.parent as YNode;
    const pcs = this.state.containers.get(parent);
    const pel = pcs === undefined ? null : $getNodeByKey(pcs.key);
    if (pcs === undefined || !$isElementNode(pel)) {
      return;
    }
    if (pcs.kind === 'i') {
      if (pcs.key === this.composingKey) {
        this.composingRead = true;
      }
      this.$setChildren(
        pel,
        this.$readInline(parent._start, null, EMPTY_FORMATS, pel),
      );
      return;
    }
    const end: Item | null = nextZoneEnd(this.state, item);
    const unit = end === null ? undefined : this.state.unitByEnd.get(end);
    if (unit === undefined) {
      return;
    }
    if (unit.kind === 'line' && this.$readLineInPlace(unit)) {
      return;
    }
    const i = pcs.units.indexOf(unit);
    if (i >= 0) {
      this.$readRegion(pcs, pel, i, i, new Set([unit]));
    }
  }

  // -------------------------------------------------------------------------
  // Block containers

  private $unitOf(
    cs: CS,
    item: Item,
    flags: {structural: boolean; tail: boolean},
  ): Unit | null {
    const passed: Item[] = [];
    let result: Unit | null = null;
    let found = false;
    const zones = this.state.zonesOf(cs.y);
    // With moves: a walk of the item's zone (leaving inline ranges).
    const view =
      zones === null ? null : new ZoneView(zones, zones.ownerOf(item), null);
    for (
      let p: Item | null = item;
      p !== null;
      p = view === null ? p.right : stepZone(view, cs.y, p, null)
    ) {
      const zone = view === null ? null : view.zone;
      if (zones !== null && zones.ownerOf(p) !== zone) {
        if (zone !== null && !zones.inRange(zone, p)) {
          // Past the end of the range: text no marker of the range ends.
          flags.structural = true;
          break;
        }
        continue;
      }
      const inline = zones === null ? null : zones.inlineRec(zone);
      if (inline !== null && p.deleted && p !== item && inline.e === p) {
        // The end of an inline range (a join's deleted marker): the line
        // goes on after the record.
        continue;
      }
      const cached = this.located.get(p);
      if (cached !== undefined) {
        result = cached;
        found = true;
        break;
      }
      passed.push(p);
      if (isEndItem(p)) {
        const u = this.state.unitByEnd.get(p);
        if (u !== undefined && u.cs === cs) {
          // Content before a node unit (concurrent typing next to an
          // inserted block) is not part of that node: regroup.
          if (p.deleted || (u.kind === 'node' && p !== item)) {
            flags.structural = true;
          }
          result = u;
          found = true;
          break;
        }
        if (!p.deleted || p !== item) {
          flags.structural = true;
        }
      }
    }
    if (!found) {
      flags.tail = true;
    }
    for (const p of passed) {
      this.located.set(p, result);
    }
    if (result === null) {
      flags.tail = true;
    }
    return result;
  }

  private $readChanges(
    cs: CS,
    el: ElementNode,
    items: Item[],
    attrUnits: Set<Unit> | undefined,
  ): void {
    const flags = {structural: false, tail: false};
    const affected = new Set<Unit>();
    const composingItems: Item[] = [];
    // A move record added or removed changes where units show: they are
    // read where ownership changed (see MoveRead), else the container is
    // read again (typing inside moved units stays an in-place read).
    if (items.some(it => isMoveItem(it)) || this.state.takeUnresolved(cs.y)) {
      if (this.$readMoves(cs, el, items, attrUnits)) {
        return;
      }
      this.state.noteMoves(cs.y);
      this.$readFull(cs, el);
      return;
    }

    for (const it of items) {
      if (isEndItem(it) && !this.state.unitByEnd.has(it) && it.deleted) {
        // inserted and deleted in the same transaction
        continue;
      }
      const u = this.$unitOf(cs, it, flags);
      if (u !== null) {
        affected.add(u);
        if (u.key !== null && u.key === this.composingKey) {
          composingItems.push(it);
        }
      }
    }
    if (attrUnits !== undefined) {
      for (const u of attrUnits) {
        affected.add(u);
        this.attrChanged.add(u);
      }
    }
    // A format item inserted or deleted changes the formats later units
    // start with: recompute them from the first such unit, until they agree
    // again past the last one, and read the units whose start changed.
    const formatUnits: Unit[] = [];
    for (const it of items) {
      if (it.content instanceof ContentFormat) {
        const u = this.located.get(it);
        if (u !== undefined && u !== null) {
          formatUnits.push(u);
        }
      }
    }
    if (formatUnits.length > 0) {
      if (this.state.zonesOf(cs.y) !== null) {
        // Units are not in document order: recompute every start
        // (positional formats) and read the units whose start changed.
        const starts = physicalStarts(this.state, cs);
        for (const u of cs.units) {
          const f = starts.get(u);
          if (f !== undefined && !sameFormats(u.start || EMPTY_FORMATS, f)) {
            u.start = f.size > 0 ? f : null;
            affected.add(u);
          }
        }
      } else {
        for (const u of recomputeUnitStarts(cs, formatUnits)) {
          affected.add(u);
        }
      }
    }
    if (
      !flags.structural &&
      !flags.tail &&
      composingItems.length > 0 &&
      (attrUnits === undefined ||
        ![...attrUnits].some(u => u.key === this.composingKey)) &&
      this.$defer(composingItems)
    ) {
      for (const u of affected) {
        if (u.key === this.composingKey) {
          affected.delete(u);
        }
      }
      if (affected.size === 0) {
        return;
      }
    }
    if ((flags.structural || flags.tail) && this.state.zonesOf(cs.y) !== null) {
      // Units can show elsewhere than their items: read where the walks of
      // the edited zones change (see MoveRead), or the whole container.
      if (!this.$readMoves(cs, el, items, attrUnits)) {
        this.$readFull(cs, el);
      }
      return;
    }
    if (!flags.structural && !flags.tail) {
      const rest = new Set<Unit>();
      for (const u of affected) {
        if (!(u.kind === 'line' && this.$readLineInPlace(u))) {
          if (u.kind !== 'node') {
            rest.add(u);
          }
        }
      }
      if (rest.size === 0) {
        return;
      }
      affected.clear();
      for (const u of rest) {
        affected.add(u);
      }
    }
    const units = cs.units;
    const index = new Map<Unit, number>();
    units.forEach((u, i) => index.set(u, i));
    const idx: number[] = [];
    for (const u of affected) {
      const i = index.get(u);
      if (i !== undefined) {
        idx.push(i);
      }
    }
    if (flags.tail) {
      idx.push(units.length);
    }
    idx.sort((a, b) => a - b);
    // Merge into ranges [i, j] (j may be units.length = the tail).
    const ranges: [number, number][] = [];
    for (const i of idx) {
      const last = ranges[ranges.length - 1];
      if (last !== undefined && i <= last[1] + 1) {
        last[1] = Math.max(last[1], i);
      } else {
        ranges.push([i, i]);
      }
    }
    // A region's read can widen into an earlier range (merging units), so
    // ranges are kept as units and located again before each read.
    const rangeUnits = ranges.map(([a, b]) => ({
      tail: b >= units.length,
      units: units.slice(a, Math.min(b + 1, units.length)),
    }));
    for (let r = rangeUnits.length - 1; r >= 0; r--) {
      const {units: us, tail} = rangeUnits[r];
      const now = cs.units;
      let a = -1;
      let b = -1;
      for (const u of us) {
        const k = now.indexOf(u);
        if (k >= 0) {
          a = a < 0 ? k : Math.min(a, k);
          b = Math.max(b, k);
        }
      }
      if (tail) {
        if (a < 0) {
          a = now.length;
        }
        b = now.length;
      }
      if (a < 0) {
        // Every unit of this range was read with a later one.
        continue;
      }
      this.$readRegion(cs, el, a, b, affected);
    }
  }

  /**
   * Defer remote inserts into the composing line or inline container: only
   * when all of them are inserted content (no deletion, format, marker), so
   * the editor's view stays Yjs minus those ids.
   */
  private $defer(items: Item[]): boolean {
    for (const it of items) {
      if (it.deleted || !it.countable || isEndItem(it)) {
        return false;
      }
    }
    for (const it of items) {
      this.deferred.push(it);
    }
    return true;
  }

  /** Read the line or inline container `key` again (composition ended). */
  $refreshComposed(key: NodeKey): boolean {
    const state = this.state;
    const unit = state.unitByKey.get(key);
    if (unit !== undefined && unit.kind === 'line') {
      if (!this.$readLineInPlace(unit)) {
        const i = unit.cs.units.indexOf(unit);
        const el = $getNodeByKey(unit.cs.key);
        if (i >= 0 && $isElementNode(el)) {
          this.$readRegion(unit.cs, el, i, i, new Set([unit]));
        }
      }
      return true;
    }
    const cs = state.csByKey.get(key);
    const el = $getNodeByKey(key);
    if (cs !== undefined && cs.kind === 'i' && $isElementNode(el)) {
      this.$setChildren(
        el,
        this.$readInline(cs.y._start, null, EMPTY_FORMATS, el),
      );
      return true;
    }
    return false;
  }

  /**
   * Read a change of move records only where ownership changed (see
   * MoveRead). False: the container must be read in full.
   */
  private $readMoves(
    cs: CS,
    el: ElementNode,
    items: Item[],
    attrUnits: Set<Unit> | undefined,
  ): boolean {
    const state = this.state;
    if (cs.kind !== 'b') {
      moveReadStats.full++;
      moveReadStats.reasons.inline = (moveReadStats.reasons.inline ?? 0) + 1;
      return false;
    }
    const had = state.hasMoves(cs.y);
    const cached = state.peekZones(cs.y);
    if (had && cached === undefined) {
      moveReadStats.full++;
      moveReadStats.reasons['no-before'] =
        (moveReadStats.reasons['no-before'] ?? 0) + 1;
      return false;
    }
    const before = had ? cached! : null;
    state.noteMoves(cs.y);
    // (Records left but none active: zonesOf has just cached the fresh
    // ownership; no record left: a fresh index.)
    const after =
      state.zonesOf(cs.y) ??
      state.peekZones(cs.y) ??
      new Zones(state.doc, cs.y);
    const plan = planMoveRead(
      state,
      cs,
      before,
      after,
      items.filter(it => isMoveItem(it)),
      attrUnits,
      items.filter(it => !isMoveItem(it)),
    );
    if (typeof plan === 'string') {
      return false;
    }
    if (!this.$applyMovePlan(cs, el, plan)) {
      moveReadStats.incremental--;
      moveReadStats.full++;
      moveReadStats.reasons['region-kind'] =
        (moveReadStats.reasons['region-kind'] ?? 0) + 1;
      return false;
    }
    return true;
  }

  /** Put the units of a move plan in place (false: nothing was changed). */
  private $applyMovePlan(cs: CS, el: ElementNode, plan: MovePlan): boolean {
    const state = this.state;
    const list = plan.units;
    const n = list.length;
    const isUnit = (e: Unit | Parsed): e is Unit => 'cs' in e;
    // Regions to materialize: runs of changed positions, and the places of
    // windows that show nothing now, widened over neighbouring group items
    // (groups next to a change are built again).
    const intervals: [number, number][] = [];
    const sorted = [...plan.changed].sort((a, b) => a - b);
    for (const k of sorted) {
      const last = intervals[intervals.length - 1];
      if (last !== undefined && last[1] === k) {
        last[1] = k + 1;
      } else {
        intervals.push([k, k + 1]);
      }
    }
    for (const g of plan.gaps) {
      intervals.push([g, g]);
    }
    const groupItem = (k: number) => {
      const e = list[k];
      return isUnit(e) && !plan.changed.has(k) && e.sig !== '';
    };
    for (const iv of intervals) {
      while (iv[0] > 0 && groupItem(iv[0] - 1)) {
        iv[0]--;
      }
      while (iv[1] < n && groupItem(iv[1])) {
        iv[1]++;
      }
    }
    intervals.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    const regions: [number, number][] = [];
    for (const iv of intervals) {
      if (iv[0] === iv[1]) {
        continue;
      }
      const last = regions[regions.length - 1];
      if (last !== undefined && iv[0] <= last[1]) {
        last[1] = Math.max(last[1], iv[1]);
      } else {
        regions.push([iv[0], iv[1]]);
      }
    }
    // Kept units that would be read again need their items' bounds: lines
    // and nodes only (else read in full; nothing was changed yet).
    for (const [a, b] of regions) {
      for (let k = a; k < b; k++) {
        const e = list[k];
        if (isUnit(e) && (e.kind === 'run' || e.kind === 'implicit')) {
          return false;
        }
      }
    }
    this.fresh.add(cs.y);
    this.rebuilt.add(cs);
    const present = new Set<Unit>();
    for (const e of list) {
      if (isUnit(e)) {
        present.add(e);
      }
    }
    const removed = plan.replaced.filter(u => !present.has(u));
    // Old units in the regions, and old units of entries read again (their
    // nodes are reused).
    // (Text no marker ends keeps the nodes of such text read before.)
    const implicit = removed.filter(u => u.end === null);
    const regionOld: Unit[][] = regions.map(([a, b]) => {
      const out: Unit[] = [];
      for (let k = a; k < b; k++) {
        const e = list[k];
        if (isUnit(e)) {
          out.push(e);
        } else if (e.end !== null) {
          const u = state.unitByEnd.get(e.end);
          if (u !== undefined && u.cs === cs && !present.has(u)) {
            out.push(u);
          }
        } else if (implicit.length > 0) {
          out.push(implicit.shift()!);
        }
      }
      return out;
    });
    if (this.composingKey !== null) {
      const touched = [...removed, ...regionOld.flat()];
      if (touched.some(u => u.key === this.composingKey)) {
        this.composingRead = true;
      }
    }
    // The Lexical children the old units covered.
    const oldTops: LexicalNode[] = [];
    const seen = new Set<NodeKey>();
    const collectTops = (u: Unit) => {
      if (u.first === null || u.last === null || seen.has(u.first)) {
        return;
      }
      const first = $getNodeByKey(u.first);
      const parent = first === null ? null : first.getParent();
      if (first === null || parent === null || !parent.is(el)) {
        return;
      }
      for (
        let t: LexicalNode | null = first;
        t !== null;
        t = t.getNextSibling()
      ) {
        if (!seen.has(t.getKey())) {
          seen.add(t.getKey());
          oldTops.push(t);
        }
        if (t.getKey() === u.last) {
          break;
        }
      }
    };
    for (const u of removed) {
      collectTops(u);
    }
    for (const us of regionOld) {
      for (const u of us) {
        collectTops(u);
      }
    }
    const pool = $newPool([...removed, ...regionOld.flat()], this.state);
    const keep = new Set<NodeKey>();
    const newUnits: Unit[] = [];
    regions.forEach(([a, b], r) => {
      const parsed: Parsed[] = [];
      const clean = new Set<Unit>();
      for (let k = a; k < b; k++) {
        const e = list[k];
        if (isUnit(e)) {
          clean.add(e);
          const zone = plan.moved.has(e)
            ? plan.moved.get(e)!
            : (e.zone ?? null);
          const bound = e.end === null ? null : prevBoundary(state, e.end);
          parsed.push({
            end: e.end,
            kind: e.kind,
            start: e.start || EMPTY_FORMATS,
            startItem: bound === null ? cs.y._start : bound.right,
            startZone: zone,
            stop: e.end,
            zone,
          });
        } else {
          parsed.push(e);
        }
      }
      const {units, tops} = this.$materialize(
        cs,
        el,
        parsed,
        regionOld[r],
        null,
        null,
        clean,
        pool,
      );
      // Where the region's nodes go: after the last node shown before it.
      let cursor: LexicalNode | null = null;
      for (let k = a - 1; k >= 0 && cursor === null; k--) {
        const u = list[k] as Unit;
        if (u.last !== null) {
          const t = $getNodeByKey(u.last);
          const parent = t === null ? null : t.getParent();
          if (t !== null && parent !== null && parent.is(el)) {
            cursor = t;
          }
        }
      }
      for (const t of tops) {
        keep.add(t.getKey());
        if (cursor === null) {
          const firstChild = el.getFirstChild();
          if (firstChild === null) {
            el.append(t);
          } else if (!firstChild.is(t)) {
            firstChild.insertBefore(t);
          }
        } else {
          const next = cursor.getNextSibling();
          if (next === null || !next.is(t)) {
            cursor.insertAfter(t);
          }
        }
        cursor = t;
      }
      for (let k = a; k < b; k++) {
        list[k] = units[k - a];
        newUnits.push(units[k - a]);
      }
    });
    for (const t of oldTops) {
      const parent = t.getParent();
      if (!keep.has(t.getKey()) && parent !== null && parent.is(el)) {
        t.remove(true);
      }
    }
    for (const u of removed) {
      state.dropUnit(u);
    }
    for (const u of newUnits) {
      state.setUnit(u);
    }
    cs.units = list as Unit[];
    if (this.$containerGroupSpec(cs) !== null) {
      state.refresh.add(cs.key);
    }
    return true;
  }

  private $readRegion(
    cs: CS,
    el: ElementNode,
    i: number,
    j: number,
    affected: ReadonlySet<Unit> | null = null,
  ): void {
    if (this.state.zonesOf(cs.y) !== null || cs.units.some(u => u.zone)) {
      this.$readFull(cs, el);
      return;
    }
    const units = cs.units;
    i = Math.min(i, units.length);
    j = Math.max(i, Math.min(j, units.length));
    this.rebuilt.add(cs);
    const len = units.length;
    const sameTop = (a: number, b: number) =>
      a >= 0 &&
      b < len &&
      units[a].first !== null &&
      units[a].first === units[b].first;
    for (;;) {
      let changed = false;
      while (j < len && units[j].end !== null && units[j].end!.deleted) {
        j++;
        changed = true;
      }
      if (j < len && units[j].end === null && j < len - 1) {
        j++;
        changed = true;
      }
      while (
        i > 0 &&
        (units[i - 1].end === null || units[i - 1].end!.deleted)
      ) {
        i--;
        changed = true;
      }
      while (i > 0 && i < len && sameTop(i - 1, i)) {
        i--;
        changed = true;
      }
      while (j < len - 1 && sameTop(j, j + 1)) {
        j++;
        changed = true;
      }
      if (!changed) {
        break;
      }
    }
    for (;;) {
      const tail = j >= len;
      const left = i > 0 ? units[i - 1].end : null;
      const startItem = left === null ? cs.y._start : left.right;
      const stop =
        j >= len ? null : units[j].end === null ? null : units[j].end!.right;
      const startFormats =
        i < len
          ? units[i].start || EMPTY_FORMATS
          : formatsAfterUnit(units, i - 1);
      const {parsed, after} = parseRange(startItem, stop, startFormats);
      // Groups next to the region may merge with it.
      const isGroupItem = (p: Parsed | undefined) =>
        p !== undefined &&
        p.kind === 'line' &&
        this.$groupOf(cs, markerAttrs(typeOf(p.end!))) !== null;
      // A region that reads back empty (its units were removed) can leave
      // two groups adjacent: read them together so they regroup as one when
      // their keys are equal.
      if (
        parsed.length === 0 &&
        !tail &&
        i > 0 &&
        Math.min(j, len - 1) + 1 < len &&
        units[i - 1].sig !== '' &&
        units[Math.min(j, len - 1) + 1].sig !== ''
      ) {
        const top = units[i - 1].first;
        while (i > 0 && units[i - 1].first === top) {
          i--;
        }
        const nextTop = units[Math.min(j, len - 1) + 1].first;
        while (j + 1 < len && units[j + 1].first === nextTop) {
          j++;
        }
        continue;
      }
      if (i > 0 && units[i - 1].sig !== '' && isGroupItem(parsed[0])) {
        const top = units[i - 1].first;
        while (i > 0 && units[i - 1].first === top) {
          i--;
        }
        continue;
      }
      const lastJ = Math.min(j, len - 1);
      if (
        !tail &&
        lastJ + 1 < len &&
        units[lastJ + 1].sig !== '' &&
        isGroupItem(parsed[parsed.length - 1])
      ) {
        const top = units[lastJ + 1].first;
        while (j + 1 < len && units[j + 1].first === top) {
          j++;
        }
        continue;
      }
      const old = units.slice(i, Math.min(j + 1, len));
      const oldFirst = old.length > 0 ? old[0].first : null;
      const oldLast = old.length > 0 ? old[old.length - 1].last : null;
      const prevLast = i > 0 ? units[i - 1].last : null;
      // The Lexical children the old units cover (before materializing,
      // which may move pooled nodes).
      let prev: LexicalNode | null = null;
      const oldTops: LexicalNode[] = [];
      if (oldFirst !== null && oldLast !== null) {
        const first = $getNodeByKey(oldFirst);
        const last = $getNodeByKey(oldLast);
        if (
          first !== null &&
          last !== null &&
          first.getParent() !== null &&
          first.getParent()!.is(el)
        ) {
          prev = first.getPreviousSibling();
          for (
            let n: LexicalNode | null = first;
            n !== null;
            n = n.getNextSibling()
          ) {
            oldTops.push(n);
            if (n.is(last)) {
              break;
            }
          }
        }
      }
      if (prev === null && oldTops.length === 0 && prevLast !== null) {
        prev = $getNodeByKey(prevLast);
      }
      const {units: fresh, tops} = this.$materialize(
        cs,
        el,
        parsed,
        old,
        affected,
        left,
      );
      const keep = new Set(tops.map(t => t.getKey()));
      for (const n of oldTops) {
        const parent = n.getParent();
        // Nodes the read moved elsewhere (reused groups) stay where they are.
        if (!keep.has(n.getKey()) && parent !== null && parent.is(el)) {
          n.remove(true);
        }
      }
      let cursor = prev;
      for (const t of tops) {
        if (cursor === null) {
          const firstChild = el.getFirstChild();
          if (firstChild === null) {
            el.append(t);
          } else if (!firstChild.is(t)) {
            firstChild.insertBefore(t);
          }
        } else {
          const next = cursor.getNextSibling();
          if (next === null || !next.is(t)) {
            cursor.insertAfter(t);
          }
        }
        cursor = t;
      }
      this.$commitUnits(cs, i, Math.min(j + 1, len), fresh, old);
      // Formats that now reach past the region change the next unit.
      const nextIndex = i + fresh.length;
      const next = cs.units[nextIndex];
      if (
        next !== undefined &&
        !sameFormats(next.start || EMPTY_FORMATS, after)
      ) {
        next.start = after.size > 0 ? after : null;
        if (next.kind !== 'line' || !this.$readLineInPlace(next)) {
          this.$readRegion(cs, el, nextIndex, nextIndex);
        }
      }
      return;
    }
  }

  private $commitUnits(
    cs: CS,
    from: number,
    to: number,
    fresh: Unit[],
    old: Unit[],
  ): void {
    const keep = new Set(fresh);
    for (const u of old) {
      if (!keep.has(u)) {
        this.state.dropUnit(u);
      }
    }
    const isIdentified = this.state.blockIds;
    for (const u of fresh) {
      this.state.setUnit(u);
      // A derived id (a line without a marker, or whose marker stores none)
      // is for identified blocks only (known once the line is in place).
      if (
        isIdentified !== null &&
        u.key !== null &&
        (u.kind === 'implicit' ||
          (u.kind === 'line' &&
            u.end !== null &&
            typeOf(u.end).getAttr(STATE_PREFIX + blockIdState.key) ===
              undefined))
      ) {
        const line = $getNodeByKey(u.key);
        if (
          line !== null &&
          $getState(line, blockIdState) !== undefined &&
          !isIdentified(line)
        ) {
          $setBlockId(line, undefined);
        }
      }
      // A stored node that stores no id has one derived from its item, if
      // it is an identified block (known once it is in place).
      if (
        isIdentified !== null &&
        u.kind === 'node' &&
        u.key !== null &&
        u.end !== null
      ) {
        const node = $getNodeByKey(u.key);
        const y = typeOf(u.end);
        this.state.noteStoredId(
          u.key,
          y.getAttr(STATE_PREFIX + blockIdState.key),
        );
        if (
          node !== null &&
          y.getAttr(STATE_PREFIX + blockIdState.key) === undefined
        ) {
          const want = isIdentified(node)
            ? storedDerivedId(node, u.end)
            : undefined;
          if ($getState(node, blockIdState) !== want) {
            $setBlockId(node, want);
          }
          this.noteDerived(want ?? null);
        }
      }
      // So is a group's (known once it is in place): a group that is not an
      // identified block (a nested list) keeps no block id, which an item's
      // marker can carry from another level or another group after
      // concurrent edits (see $withoutOuterId).
      if (isIdentified !== null && u.sig !== '' && u.key !== null) {
        const line = $getNodeByKey(u.key);
        let g = line === null ? null : line.getParent();
        while ($isElementNode(g) && getGroupSpec(klassOf(g)) !== null) {
          if ($getState(g, blockIdState) !== undefined && !isIdentified(g)) {
            $setBlockId(g, undefined);
          }
          const w: ElementNode | null = g.getParent();
          g = w === null ? null : w.getParent();
        }
      }
    }
    spliceAll(cs.units, from, to - from, fresh);
    // A container that is a group itself (stored as a node) recomputes its
    // items' derived fields too.
    if (this.$containerGroupSpec(cs) !== null) {
      this.state.refresh.add(cs.key);
    }
  }

  /**
   * Recompute the start formats of every unit of a container holding moves
   * from the shared items (positional formats), and read again the units
   * whose start changed.
   */
  private $fixZonedStarts(cs: CS): void {
    const starts = physicalStarts(this.state, cs);
    const changed: Unit[] = [];
    for (const u of cs.units) {
      const f = starts.get(u);
      if (f !== undefined && !sameFormats(u.start || EMPTY_FORMATS, f)) {
        u.start = f.size > 0 ? f : null;
        changed.push(u);
      }
    }
    for (const u of changed) {
      if (u.kind !== 'line' || !this.$readLineInPlace(u)) {
        const el = $getNodeByKey(cs.key);
        if ($isElementNode(el)) {
          this.$readFull(cs, el);
        }
        return;
      }
    }
  }

  private $readLineInPlace(u: Unit): boolean {
    const line = u.key === null ? null : $getNodeByKey(u.key);
    if (!$isElementNode(line) || u.end === null || u.end.deleted) {
      return false;
    }
    let attrs = markerAttrs(typeOf(u.end));
    if (attrs[TYPE_KEY] !== line.getType()) {
      return false;
    }
    this.state.noteStoredId(
      line.getKey(),
      attrs[STATE_PREFIX + blockIdState.key],
    );
    const isIdentified = this.state.blockIds;
    if (
      isIdentified !== null &&
      attrs[STATE_PREFIX + blockIdState.key] === undefined &&
      isIdentified(line)
    ) {
      attrs = {
        ...attrs,
        [STATE_PREFIX + blockIdState.key]: derivedBlockId(u.end),
      };
      this.noteDerived(derivedBlockId(u.end));
    }
    const group = this.$groupOf(u.cs, attrs);
    if (groupSig(attrs, group) !== u.sig) {
      return false;
    }
    if (u.key === this.composingKey) {
      this.composingRead = true;
    }
    this.$applyLineAttrs(
      line,
      attrs,
      this.$derivedFor(u.cs, group),
      this.attrChanged.has(u),
    );
    const zones = this.state.zonesOf(u.cs.y);
    const {left, zone: startZone} = lineStart(this.state, u.end);
    this.$setChildren(
      line,
      this.$readInline(
        startItemAfter(zones, u.cs.y, left, startZone),
        u.end,
        u.start || EMPTY_FORMATS,
        line,
        undefined,
        this.zv(u.cs, startZone),
      ),
    );
    // A format that now reaches past the marker changes the next unit.
    const after = this.lastFormats;
    if (zones !== null) {
      // The units that start right after its marker (the next one of its
      // zone, and the first unit of a range that starts there) start with
      // the formats after it. When one of them disagrees, every start of
      // the container is recomputed (formats are positional) and the units
      // whose start changed are read again.
      const nextEnd = nextZoneEnd(this.state, u.end);
      const next =
        nextEnd === null ? undefined : this.state.unitByEnd.get(nextEnd);
      let stale =
        next !== undefined && !sameFormats(next.start || EMPTY_FORMATS, after);
      if (!stale) {
        for (const r of zones.active) {
          if (r.s === u.end) {
            const first = u.cs.units.find(x => x.zone === r.item);
            if (
              first !== undefined &&
              !sameFormats(first.start || EMPTY_FORMATS, after)
            ) {
              stale = true;
            }
          }
        }
      }
      if (stale) {
        this.$fixZonedStarts(u.cs);
      }
      // A range shown inline that starts right after the marker takes its
      // formats from there: the line showing it is read again.
      for (const r of zones.active) {
        if (r.inline === true && r.s === u.end && !this.inlineReads.has(r)) {
          const e = nextZoneEnd(zones, r.item, zones.ownerOf(r.item));
          const shower = e === null ? undefined : this.state.unitByEnd.get(e);
          if (shower !== undefined && shower !== u && shower.kind === 'line') {
            this.inlineReads.add(r);
            if (!this.$readLineInPlace(shower)) {
              return false;
            }
          }
        }
      }
      return true;
    }
    let nextEnd: Item | null = u.end.right;
    while (nextEnd !== null && (nextEnd.deleted || !isEndItem(nextEnd))) {
      nextEnd = nextEnd.right;
    }
    const next =
      nextEnd === null ? undefined : this.state.unitByEnd.get(nextEnd);
    if (
      next !== undefined &&
      !sameFormats(next.start || EMPTY_FORMATS, after)
    ) {
      next.start = after.size > 0 ? new Map(after) : null;
      if (next.kind !== 'line' || !this.$readLineInPlace(next)) {
        const el = $getNodeByKey(next.cs.key);
        const i = next.cs.units.indexOf(next);
        if ($isElementNode(el) && i >= 0) {
          this.$readRegion(next.cs, el, i, i);
        }
      }
    }
    return true;
  }

  // -------------------------------------------------------------------------
  // Materializing units

  private $containerGroupSpec(cs: CS): GroupSpec | null {
    const el = $getNodeByKey(cs.key);
    return el === null ? null : getContainerGroupSpec(klassOf(el));
  }

  private $derivedFor(
    cs: CS,
    group: GroupItemInfo | null,
  ): ReadonlySet<string> | null {
    if (group !== null) {
      return group.spec.derived;
    }
    const spec = this.$containerGroupSpec(cs);
    return spec === null ? null : spec.derived;
  }

  /** The group a marker puts its line in, or null. */
  private $groupOf(cs: CS, attrs: Attrs): GroupItemInfo | null {
    if (this.$containerGroupSpec(cs) !== null) {
      return null;
    }
    const type = attrs[TYPE_KEY];
    const info =
      typeof type === 'string' ? this.state.editor._nodes.get(type) : undefined;
    if (info === undefined || getLineSpec(info.klass) === null) {
      return null;
    }
    const g = attrs[GROUP_KEY];
    const ginfo =
      typeof g === 'string' ? this.state.editor._nodes.get(g) : undefined;
    if (typeof g === 'string' && ginfo === undefined) {
      this.state.unknownTypes.add(g);
    }
    const spec = ginfo === undefined ? null : getGroupSpec(ginfo.klass);
    if (spec !== null && spec.items.includes(info.klass)) {
      const gkey: Attrs = {};
      for (const k in attrs) {
        if (k.startsWith(GROUP_FIELD_PREFIX)) {
          gkey[k] = attrs[k];
        }
      }
      // The level as written: the writer records the outer levels with it
      // (one entry each), so a level whose record matches is read at any
      // depth. One without a matching record (concurrent writes of the two
      // keys, or a writer that kept no record) is capped: its outer levels
      // are not known, and each costs memory.
      const raw = attrs[LEVEL_KEY];
      const o = attrs[OUTER_KEY];
      const level =
        typeof raw === 'number' && Number.isInteger(raw) && raw > 0
          ? Array.isArray(o) && o.length === raw
            ? raw
            : Math.min(64, raw)
          : 0;
      const outer =
        level > 0 &&
        Array.isArray(o) &&
        o.length === level &&
        o.every(v => v !== null && typeof v === 'object' && !Array.isArray(v))
          ? (o as Attrs[])
          : null;
      return {gkey, gtype: g as string, level, outer, spec};
    }
    // An item of a group outside any group: Lexical would wrap it.
    const fallback = this.$defaultGroup(info.klass);
    return fallback === null
      ? null
      : {
          gkey: {},
          gtype: fallback.klass.getType(),
          level: 0,
          outer: null,
          spec: fallback,
        };
  }

  private $defaultGroup(item: Klass<LexicalNode>): GroupSpec | null {
    for (const {klass} of this.state.editor._nodes.values()) {
      const spec = getGroupSpec(klass);
      if (spec !== null && spec.klass === klass && spec.items.includes(item)) {
        return spec;
      }
    }
    return null;
  }

  private $materialize(
    cs: CS,
    el: ElementNode,
    parsed: Parsed[],
    old: Unit[],
    affected: ReadonlySet<Unit> | null = null,
    left: Item | null = null,
    clean: ReadonlySet<Unit> | null = null,
    sharedPool: Pool | null = null,
  ): {units: Unit[]; tops: LexicalNode[]} {
    const state = this.state;
    // The end before each old unit, to tell a line whose range did not change.
    const prevEnd = new Map<Unit, Item | null>();
    old.forEach((u, k) => prevEnd.set(u, k === 0 ? left : old[k - 1].end));
    let parsedPrevEnd: Item | null = left;
    const byEnd = new Map<Item, Unit>();
    const implicit: Unit[] = [];
    for (const u of old) {
      if (u.end !== null) {
        byEnd.set(u.end, u);
      } else {
        implicit.push(u);
      }
    }
    // The line being composed (IME) that a remote change merges into the
    // next line (its marker was deleted) keeps its node for the merged line:
    // the browser's composition stays in its DOM.
    let composedLine: {into: Unit; key: NodeKey} | null = null;
    const ck = this.composingKey;
    // Whether the line being composed is among the units read, and whether
    // it kept its range and content (untouched below): only then does what
    // is hidden in it stay hidden (see composingRead).
    const composedOld = ck !== null && old.some(u => u.key === ck);
    let composedKept = false;
    if (ck !== null && this.state.editor._compositionKey !== null) {
      const k = old.findIndex(u => u.key === ck);
      if (k >= 0 && old[k].end !== null && old[k].end!.deleted) {
        let j = k + 1;
        while (j < old.length && old[j].end !== null && old[j].end!.deleted) {
          j++;
        }
        if (j < old.length && old[j].end !== null && old[j].kind === 'line') {
          composedLine = {into: old[j], key: ck};
        }
      }
    }
    const pool: Pool = sharedPool ?? $newPool(old, state);
    type Entry = {unit: Unit; nodes: LexicalNode[]; group: GroupItem | null};
    const entries: Entry[] = [];
    for (const p of parsed) {
      if (p.kind === 'node') {
        const y = typeOf(p.end!);
        let node = this.$storedNode(y);
        if (node === null) {
          node = this.$createStored(y);
        }
        const prevUnit = byEnd.get(p.end!);
        const unit: Unit = prevUnit || {
          cs,
          end: p.end,
          first: null,
          key: null,
          kind: 'node',
          last: null,
          sig: '',
          start: null,
        };
        unit.key = node === null ? null : node.getKey();
        unit.first = unit.last = unit.key;
        unit.sig = '';
        unit.zone = p.zone;
        // Its start formats (a format can span a block node: the following
        // units' reads start from this value).
        unit.start = p.start.size > 0 ? p.start : null;
        entries.push({group: null, nodes: node === null ? [] : [node], unit});
        parsedPrevEnd = p.end;
        continue;
      }
      if (p.kind === 'run') {
        const prevUnit = byEnd.get(p.end!);
        const poolNodes: LexicalNode[] = [];
        if (prevUnit !== undefined && prevUnit.first !== null) {
          for (
            let n = $getNodeByKey(prevUnit.first);
            n !== null;
            n = n.getNextSibling()
          ) {
            poolNodes.push(n);
            if (n.getKey() === prevUnit.last) {
              break;
            }
          }
        }
        const nodes = this.$readInline(
          p.startItem,
          p.stop,
          p.start,
          null,
          poolNodes,
          this.zv(cs, p.startZone),
        );
        const unit: Unit = prevUnit || {
          cs,
          end: p.end,
          first: null,
          key: null,
          kind: 'run',
          last: null,
          sig: '',
          start: null,
        };
        unit.kind = 'run';
        unit.start = p.start.size > 0 ? p.start : null;
        unit.zone = p.zone;
        entries.push({group: null, nodes, unit});
        parsedPrevEnd = p.end;
        continue;
      }
      // line or implicit line
      // Text without a marker reads as a paragraph, or in a container that
      // is a group itself (a list stored as a node) as an item of the group:
      // the class Lexical would wrap it in, on every reader. With block ids,
      // its id is derived from its first character (see implicitBlockId).
      const containerGroup = this.$containerGroupSpec(cs);
      let attrs: Attrs =
        p.kind === 'line'
          ? markerAttrs(typeOf(p.end!))
          : {
              [TYPE_KEY]:
                containerGroup === null
                  ? 'paragraph'
                  : containerGroup.items[0].getType(),
            };
      // A line of another type in a container that is a group itself (a
      // quote in a list stored as a node, left by concurrent edits) reads as
      // an item of the group holding its content, as Lexical converts a block
      // put into the group (ListNode.splice), on every reader. A type this
      // editor does not register as a line is not converted: it makes the
      // binding read only (see $lineFromMarker), so that what it holds is
      // never rewritten as another type.
      if (containerGroup !== null && p.kind === 'line') {
        const info = this.state.editor._nodes.get(String(attrs[TYPE_KEY]));
        if (
          info !== undefined &&
          getLineSpec(info.klass) !== null &&
          !containerGroup.items.includes(info.klass)
        ) {
          attrs = {[TYPE_KEY]: containerGroup.items[0].getType()};
        }
      }
      // A line whose marker stores no block id (written without
      // BlockIdExtension, or by a client whose naming was not written) has
      // one derived from Yjs identity, as a line without a marker does: the
      // same on every reader, and stored by the next write of the line.
      const storedId = attrs[STATE_PREFIX + blockIdState.key];
      const derivedId =
        this.state.blockIds === null
          ? null
          : p.kind === 'implicit'
            ? implicitBlockId(p.startItem, p.stop)
            : derivedBlockId(p.end!);
      if (
        derivedId !== null &&
        attrs[STATE_PREFIX + blockIdState.key] === undefined
      ) {
        attrs = {...attrs, [STATE_PREFIX + blockIdState.key]: derivedId};
        this.noteDerived(derivedId);
      }
      const prevUnit = p.end !== null ? byEnd.get(p.end) : implicit.shift();
      const merged =
        composedLine !== null && prevUnit === composedLine.into
          ? $getNodeByKey(composedLine.key)
          : null;
      const existing =
        merged !== null
          ? merged
          : prevUnit !== undefined && prevUnit.key !== null
            ? $getNodeByKey(prevUnit.key)
            : null;
      const ginfo = this.$groupOf(cs, attrs);
      const derived = this.$derivedFor(cs, ginfo);
      // A line the change did not touch (pulled in to regroup) keeps its
      // node, attributes and content.
      const untouched =
        merged === null &&
        prevUnit !== undefined &&
        p.end !== null &&
        prevUnit.end === p.end &&
        $isElementNode(existing) &&
        existing.getType() === attrs[TYPE_KEY] &&
        // Its content is known not to have changed (it only moved).
        ((clean !== null && clean.has(prevUnit)) ||
          (affected !== null &&
            (prevUnit.zone ?? null) === p.zone &&
            prevEnd.get(prevUnit) === parsedPrevEnd &&
            !affected.has(prevUnit) &&
            sameFormats(prevUnit.start || EMPTY_FORMATS, p.start)));
      const line = untouched
        ? (existing as ElementNode)
        : this.$lineFromMarker(
            attrs,
            $isElementNode(existing) ? existing : null,
            derived,
          );
      if (untouched && prevUnit !== undefined && prevUnit.key === ck) {
        composedKept = true;
      }
      state.noteStoredId(line.getKey(), storedId);
      if (!untouched) {
        this.$setChildren(
          line,
          this.$readInline(
            p.startItem,
            p.stop,
            p.start,
            line,
            merged !== null && prevUnit !== undefined && prevUnit.key !== null
              ? (() => {
                  const into = $getNodeByKey(prevUnit.key);
                  return $isElementNode(into) && !into.is(line)
                    ? into.getChildren()
                    : undefined;
                })()
              : $isElementNode(existing) && !existing.is(line)
                ? existing.getChildren()
                : undefined,
            this.zv(cs, p.startZone),
          ),
        );
      }
      const unit: Unit = prevUnit || {
        cs,
        end: p.end,
        first: null,
        key: null,
        kind: p.kind,
        last: null,
        sig: '',
        start: null,
      };
      unit.kind = p.kind;
      unit.end = p.end;
      unit.key = line.getKey();
      unit.zone = p.zone;
      unit.start = p.start.size > 0 ? p.start : null;
      unit.sig = groupSig(attrs, ginfo);
      unit.first = unit.last = unit.key;
      const group: GroupItem | null =
        ginfo === null
          ? null
          : {
              // Groups are identified blocks only at the root's top level
              // (BlockIdExtension's default): a group elsewhere gets none.
              derivedId: cs.y === state.root ? derivedId : null,

              gkey: ginfo.gkey,
              gsig: ginfo.gtype + '\u0000' + stableStringify(ginfo.gkey),
              gtype: ginfo.gtype,
              keys: [
                ...(ginfo.outer === null
                  ? new Array<null>(ginfo.level).fill(null)
                  : ginfo.outer.map(keyFromFields)),
                ginfo.gkey,
              ],
              level: ginfo.level,
              node: line,
              spec: ginfo.spec,
              wrappers:
                ginfo.outer === null
                  ? []
                  : ginfo.outer.map(o => {
                      const w = o[WRAPPER_FIELDS_KEY];
                      return w !== null &&
                        typeof w === 'object' &&
                        !Array.isArray(w)
                        ? (w as Attrs)
                        : null;
                    }),
            };
      pool.lines.add(line.getKey());
      entries.push({group, nodes: [line], unit});
      parsedPrevEnd = p.end;
    }
    // Tops: consecutive group items form groups.
    const tops: LexicalNode[] = [];
    for (let k = 0; k < entries.length; ) {
      const e = entries[k];
      if (e.group === null) {
        for (const n of e.nodes) {
          tops.push(n);
        }
        if (e.nodes.length > 0) {
          e.unit.first = e.nodes[0].getKey();
          e.unit.last = e.nodes[e.nodes.length - 1].getKey();
        }
        k++;
        continue;
      }
      let m = k;
      const items: GroupItem[] = [];
      while (m < entries.length && entries[m].group !== null) {
        items.push(entries[m].group!);
        m++;
      }
      const groups = this.$buildGroups(items, 0, pool);
      const groupSet = new Set(groups.map(g => g.getKey()));
      for (let t = k; t < m; t++) {
        let n: LexicalNode = entries[t].group!.node;
        while (n.getParent() !== null && !groupSet.has(n.getKey())) {
          n = n.getParent()!;
        }
        entries[t].unit.first = entries[t].unit.last = n.getKey();
      }
      for (const g of groups) {
        tops.push(g);
      }
      k = m;
    }
    if (composedOld && !composedKept) {
      this.composingRead = true;
    }
    return {tops, units: entries.map(e => e.unit)};
  }

  private $buildGroups(
    items: GroupItem[],
    level: number,
    pool: Pool,
    ranges: [number, number][] = [],
    outerIds: ReadonlySet<string> = NO_IDS,
  ): ElementNode[] {
    const groups: ElementNode[] = [];
    // The key of a group at this level: an item's own key at its level, the
    // recorded outer key of a deeper item (null when not recorded).
    // Groups are told apart by their first declared key field only (a list
    // by its type: Lexical merges adjacent lists of one type whatever their
    // start), so a tree read back never has two adjacent groups Lexical
    // would merge. Items whose other group fields differ (written
    // concurrently) share one group, whose fields come from its first item.
    const keyAt = (x: GroupItem): string | null => {
      const k = x.keys[level];
      if (k === null || k === undefined) {
        return null;
      }
      const key: Attrs = {};
      for (const f of x.spec.key) {
        const v = k[GROUP_FIELD_PREFIX + f];
        if (v !== undefined) {
          key[f] = v;
        }
      }
      return x.gtype + '\u0000' + stableStringify(key);
    };
    let i = 0;
    while (i < items.length) {
      let keyItem = items[i];
      let sig = keyAt(keyItem);
      let j = i + 1;
      while (j < items.length) {
        const s = keyAt(items[j]);
        if (
          items[j].level > level
            ? s !== null && sig !== null && s !== sig
            : s !== sig && sig !== null
        ) {
          break;
        }
        if (sig === null && s !== null) {
          // The first item that records this level's key decides it.
          sig = s;
          keyItem = items[j];
        }
        j++;
      }
      const k = keyItem.keys[level];
      const group = this.$createGroup(
        k === null || k === undefined ? items[i] : {...keyItem, gkey: k},
        pool,
        outerIds,
        level === 0 ? items[i].derivedId : null,
      );
      this.state.refresh.add(group.getKey());
      const id = $getState(group, blockIdState);
      const kids = this.$groupChildren(
        items.slice(i, j),
        level,
        pool,
        typeof id === 'string' ? new Set([...outerIds, id]) : outerIds,
      );
      $detachFromKids(group, kids);
      this.$setChildren(group, kids);
      groups.push(group);
      ranges.push([i, j]);
      i = j;
    }
    return groups;
  }

  private $groupChildren(
    items: GroupItem[],
    level: number,
    pool: Pool,
    outerIds: ReadonlySet<string>,
  ): LexicalNode[] {
    const out: LexicalNode[] = [];
    let i = 0;
    while (i < items.length) {
      if (items[i].level <= level) {
        out.push(items[i].node);
        i++;
        continue;
      }
      let j = i;
      while (j < items.length && items[j].level > level) {
        j++;
      }
      const ranges: [number, number][] = [];
      const built = this.$buildGroups(
        items.slice(i, j),
        level + 1,
        pool,
        ranges,
        outerIds,
      );
      for (let gi = 0; gi < built.length; gi++) {
        const g = built[gi];
        const spec = items[i].spec;
        // The group keeps the wrapper that holds it (a full read of an
        // unchanged document gives back the same nodes, and the selection in
        // them stays where it is). Otherwise a pooled wrapper, which must not
        // be a line of this read, the group it will hold, or one of its
        // ancestors (that would build a cycle).
        const own = g.getParent();
        let wrapper: ElementNode | undefined;
        if (
          own !== null &&
          pool.levelKeys.has(own.getKey()) &&
          !pool.lines.has(own.getKey()) &&
          klassOf(own) === spec.items[0]
        ) {
          wrapper = own;
        } else {
          do {
            wrapper = pool.levels.shift();
          } while (
            wrapper !== undefined &&
            (!pool.levelKeys.has(wrapper.getKey()) ||
              pool.lines.has(wrapper.getKey()) ||
              wrapper.is(g) ||
              wrapper.isParentOf(g) ||
              klassOf(wrapper) !== spec.items[0])
          );
        }
        if (wrapper !== undefined) {
          pool.levelKeys.delete(wrapper.getKey());
        }
        // The wrapper's fields, as the first item of its group records them.
        let fields: Attrs = {};
        for (let k = i + ranges[gi][0]; k < i + ranges[gi][1]; k++) {
          const w = items[k].wrappers[level];
          if (w !== null && w !== undefined) {
            fields = w;
            break;
          }
        }
        const clean: Attrs = {};
        for (const f in fields) {
          if (!isUnsafeKey(f)) {
            clean[f] = fields[f];
          }
        }
        // The wrapper item's block id, as stored (in its nested items' outer
        // keys), or derived from its first nested item when none is (see
        // derivedBlockId).
        const wst = clean.$;
        const wstObj =
          wst !== null && typeof wst === 'object' && !Array.isArray(wst)
            ? (wst as Attrs)
            : null;
        const wrapperStoredId =
          wstObj === null ? undefined : wstObj[blockIdState.key];
        const firstDerived = items[i + ranges[gi][0]].derivedId;
        if (
          this.state.blockIds !== null &&
          wrapperStoredId === undefined &&
          firstDerived !== null
        ) {
          clean.$ = {
            ...(wstObj || {}),
            [blockIdState.key]: firstDerived + wrapperSuffix(level),
          };
          this.noteDerived(firstDerived + wrapperSuffix(level));
        }
        if (wrapper === undefined) {
          wrapper = $parseSerializedNode({
            ...clean,
            children: [],
            type: spec.items[0].getType(),
            version: 1,
          } as unknown as SerializedLexicalNode) as ElementNode;
          $setTextFields(wrapper, clean);
        } else if (
          stableStringify($levelItemFields(wrapper, spec)) !==
          stableStringify(clean)
        ) {
          const json = $schemaJSON(wrapper);
          for (const f in $levelItemFields(wrapper, spec)) {
            delete json[f];
          }
          Object.assign(json, clean);
          json.$ = clean.$ || {};
          json.type = wrapper.getType();
          wrapper = wrapper.updateFromJSON(
            json as Parameters<ElementNode['updateFromJSON']>[0],
          );
        }
        $setTextFields(wrapper, clean);
        $detachFromKids(wrapper, [g]);
        this.$setChildren(wrapper, [g]);
        this.state.noteStoredId(wrapper.getKey(), wrapperStoredId);
        out.push(wrapper);
      }
      i = j;
    }
    return out;
  }

  private $createGroup(
    item: GroupItem,
    pool: Pool,
    outerIds: ReadonlySet<string>,
    derivedId: string | null,
  ): ElementNode {
    const list = pool.groups.get(item.gtype);
    const fields: Attrs = {};
    for (const k in item.gkey) {
      const f = k.slice(GROUP_FIELD_PREFIX.length);
      if (!isUnsafeKey(f)) {
        fields[f] = item.gkey[k];
      }
    }
    // A group's state is its own level's: a nested group never takes the
    // block id of a group it is inside (an item's marker keys are written
    // one by one, so concurrent writes at two levels can leave an outer
    // group's id on a nested item; see $withoutOuterId).
    // In the index of who stores what, though, it holds the id as stored
    // (see $storedIdNow): settling gives it the id it shows (its derived id
    // when the outer group shows that one), like any block that repeats an
    // id, on every reader.
    const storedId = groupBlockId(fields) ?? undefined;
    $withoutOuterId(fields, outerIds);
    // A group whose items store no id has one derived from its first item,
    // as a line has (an identified group only: see $commitUnits).
    if (this.state.blockIds !== null && derivedId !== null) {
      const st = fields.$;
      const stObj =
        st !== null && typeof st === 'object' && !Array.isArray(st)
          ? (st as Attrs)
          : {};
      if (stObj[blockIdState.key] === undefined) {
        fields.$ = {...stObj, [blockIdState.key]: derivedId + groupSuffix(0)};
        this.noteDerived(derivedId + groupSuffix(0));
      }
    }
    // Prefer a pooled group with the same fields, then the same key fields
    // (a list of the same type keeps its node).
    const want = stableStringify(fields);
    let reused: ElementNode | undefined;
    if (list !== undefined && list.length > 0) {
      let at = list.findIndex(
        g => stableStringify($groupFields(g, item.spec)) === want,
      );
      if (at < 0) {
        at = list.findIndex(g => {
          const json = $schemaJSON(g);
          return item.spec.key.every(
            f => stableStringify(json[f]) === stableStringify(fields[f]),
          );
        });
      }
      reused = list.splice(Math.max(0, at), 1)[0];
    }
    if (reused !== undefined) {
      const current = $groupFields(reused, item.spec);
      if (stableStringify(current) !== want) {
        const json = $schemaJSON(reused);
        for (const f in current) {
          delete json[f];
        }
        Object.assign(json, fields);
        json.$ = fields.$ || {};
        json.type = reused.getType();
        reused.updateFromJSON(
          json as Parameters<ElementNode['updateFromJSON']>[0],
        );
        $setTextFields(reused, fields);
      }
      this.state.noteStoredId(reused.getKey(), storedId);
      return reused.getLatest();
    }
    const created = $parseSerializedNode({
      children: [],
      type: item.gtype,
      version: 1,
      ...fields,
    } as unknown as SerializedLexicalNode) as ElementNode;
    $setTextFields(created, fields);
    this.state.noteStoredId(created.getKey(), storedId);
    return created;
  }

  private $lineFromMarker(
    attrs: Attrs,
    existing: ElementNode | null,
    derived: ReadonlySet<string> | null,
  ): ElementNode {
    let type = attrs[TYPE_KEY];
    const info =
      typeof type === 'string' ? this.state.editor._nodes.get(type) : undefined;
    if (info === undefined || getLineSpec(info.klass) === null) {
      this.state.unknownTypes.add(String(type));
      type = 'paragraph';
      attrs = {[TYPE_KEY]: 'paragraph'};
    }
    if (existing !== null && existing.getType() === type) {
      this.$applyLineAttrs(existing, attrs, derived);
      return existing.getLatest();
    }
    const json = lineJSON(attrs, derived, type as string);
    return $parseSerializedNode(
      json as unknown as SerializedLexicalNode,
    ) as ElementNode;
  }

  /**
   * Set a line's fields and NodeState from its marker. `force`: the marker's
   * attributes changed in this transaction, so the fields are set even when
   * exportJSON shows no difference (a field exportJSON hides in the node's
   * current context, like `checked` outside a check list, must still follow
   * the marker).
   */
  private $applyLineAttrs(
    node: ElementNode,
    attrs: Attrs,
    derived: ReadonlySet<string> | null,
    force = false,
  ): void {
    const spec = getLineSpec(klassOf(node));
    if (spec === null) {
      return;
    }
    const current = $lineAttrs(node, derived);
    let same = true;
    const incoming: Attrs = {};
    for (const k of Object.keys(attrs).sort()) {
      if (isLineFieldKey(k, spec.fields, derived)) {
        incoming[k] = attrs[k];
      }
    }
    for (const k in incoming) {
      if (stableStringify(incoming[k]) !== stableStringify(current[k])) {
        same = false;
      }
    }
    for (const k in current) {
      if (k !== TYPE_KEY && !(k in incoming)) {
        same = false;
      }
    }
    if (same && !force) {
      return;
    }
    const json = $schemaJSON(node.getLatest());
    for (const f of spec.fields) {
      if (derived === null || !derived.has(f)) {
        delete json[f];
      }
    }
    const state: Attrs = {};
    for (const k in incoming) {
      if (k.startsWith(STATE_PREFIX)) {
        state[k.slice(STATE_PREFIX.length)] = incoming[k];
      } else {
        json[k.slice(FIELD_PREFIX.length)] = incoming[k];
      }
    }
    // Always stored (see $lineAttrs): absent means the default.
    if (spec.fields.has('textFormat') && json.textFormat === undefined) {
      json.textFormat = 0;
    }
    if (spec.fields.has('textStyle') && json.textStyle === undefined) {
      json.textStyle = '';
    }
    json.type = node.getType();
    const writable = node.updateFromJSON(
      json as Parameters<ElementNode['updateFromJSON']>[0],
    );
    $setStateInOrder(writable, state);
  }

  private $applyNodeAttrs(node: LexicalNode, y: YNode, placed = true): void {
    if (storedTypeOf(y) !== node.getType()) {
      // Replaced in place by a node of another type: same shared node.
      this.$retypeStored(node, y);
      return;
    }
    // The id it stores, in the index of who stores what (a change of the
    // attribute alone is settled like any other: see $settleIds).
    this.state.noteStoredId(
      node.getKey(),
      y.getAttr(STATE_PREFIX + blockIdState.key),
    );
    const attrs = this.$withDerivedId(node, y, y.getAttrs() as Attrs, placed);
    const json = joinSetMembersInJSON(
      nodeJSONFromAttrs(node.getType(), attrs),
      this.state.editor,
    );
    if ($isElementNode(node)) {
      // Always stored (see $nodeAttrs): absent means the default.
      json.textFormat = json.textFormat ?? 0;
      json.textStyle = json.textStyle ?? '';
    }
    // Compare in the stored encoding (compact, textFormat always kept).
    const owned = (x: Attrs) => {
      const out: Attrs = {};
      for (const k of Object.keys(x).sort()) {
        if (k.startsWith(FIELD_PREFIX) || k.startsWith(STATE_PREFIX)) {
          out[k] = x[k];
        }
      }
      return stableStringify(out);
    };
    const differs = owned($nodeAttrs(node)) !== owned(attrs);
    if (differs) {
      $applyJSON(node, json);
      if (
        $isElementNode(node) &&
        getGroupSpec(klassOf(node.getLatest())) !== null
      ) {
        // A group's fields changed (a list's start or type): its items'
        // derived fields are recomputed in the refresh after the read.
        this.state.refresh.add(node.getKey());
      }
    }
  }

  /**
   * A stored node's attributes, with the block id derived from its item
   * (see derivedBlockId) when it stores none and is an identified block.
   * `placed`: the node is where the read shows it; otherwise (a read that
   * places it next) a derived id it has is kept, and $commitUnits decides
   * once it is in place.
   */
  private $withDerivedId(
    node: LexicalNode,
    y: YNode,
    attrs: Attrs,
    placed: boolean,
  ): Attrs {
    const isIdentified = this.state.blockIds;
    const k = STATE_PREFIX + blockIdState.key;
    if (isIdentified === null || attrs[k] !== undefined || y._item === null) {
      return attrs;
    }
    const derived = storedDerivedId(node, y._item);
    const keep = placed
      ? node.isAttached() && isIdentified(node)
      : $getState(node, blockIdState) === derived;
    if (keep) {
      this.noteDerived(derived);
    }
    return keep ? {...attrs, [k]: derived} : attrs;
  }

  /** Replace a stored node whose type changed; its content moves along. */
  private $retypeStored(node: LexicalNode, y: YNode): void {
    const type = storedTypeOf(y);
    const info = this.state.editor._nodes.get(type);
    if (info === undefined) {
      this.state.unknownTypes.add(type);
      return;
    }
    const attrs = y.getAttrs() as Attrs;
    const json = joinSetMembersInJSON(
      nodeJSONFromAttrs(type, attrs),
      this.state.editor,
    );
    if ($isElementNode(node)) {
      json.children = [];
    }
    const next = $parseSerializedNode(json as unknown as SerializedLexicalNode);
    if ($isElementNode(node) && $isElementNode(next)) {
      $appendAll(next, node.getChildren());
    }
    const oldKey = node.getKey();
    this.state.yByKey.delete(oldKey);
    this.state.csByKey.delete(oldKey);
    $replaceStored(node, next);
    this.state.mapNode(next.getKey(), y);
    this.state.noteStoredId(
      next.getKey(),
      attrs[STATE_PREFIX + blockIdState.key],
    );
    // Lexical keeps a node's slots with it: the new node takes the stored ones.
    $readSlots(this, next, y, attrs);
  }

  /**
   * The node that shows a stored node, with its stored fields, NodeState and
   * named slots: a read shows a node as stored even where an update that was
   * not written changed it (a follow-up the binding refused, whose
   * containers are read again: BlockIdExtension may have named a block that
   * the refused change moved, a transform may have set a slot, and that node
   * keeps its key).
   */
  private $storedNode(y: YNode): LexicalNode | null {
    const key = this.state.keyByY.get(y);
    const node = key === undefined ? null : $getNodeByKey(key);
    if (node === null) {
      return null;
    }
    this.$applyNodeAttrs(node, y, false);
    const now = this.state.keyByY.get(y);
    const shown = now === undefined ? null : $getNodeByKey(now);
    if (shown !== null) {
      // And its named slots (an update not written may have set one).
      $readSlots(this, shown, y);
    }
    return shown;
  }

  /** Create a stored node (and read its container) from its Y.Node. */
  $createStored(y: YNode): LexicalNode | null {
    const type = storedTypeOf(y);
    const info = this.state.editor._nodes.get(type);
    if (info === undefined) {
      this.state.unknownTypes.add(type);
      return null;
    }
    const attrs = y.getAttrs() as Attrs;
    const json = joinSetMembersInJSON(
      nodeJSONFromAttrs(type, attrs),
      this.state.editor,
    );
    const isElement = typeof attrs[KIND_KEY] === 'string';
    if (isElement) {
      json.children = [];
    }
    const node = $parseSerializedNode(json as unknown as SerializedLexicalNode);
    this.state.mapNode(node.getKey(), y);
    // It shows the id it stores: in the index of who stores what.
    this.state.noteStoredId(
      node.getKey(),
      attrs[STATE_PREFIX + blockIdState.key],
    );
    if ($isElementNode(node)) {
      const kind: Kind = attrs[KIND_KEY] === 'i' ? 'i' : 'b';
      const cs = this.state.newCS(y, node.getKey(), kind);
      this.$readFull(cs, node);
    }
    $readSlots(this, node, y, attrs);
    return node;
  }

  // -------------------------------------------------------------------------
  // Inline content

  private $pieces(
    start: Item | null,
    stop: Item | null,
    formats: Formats,
    zv: ZoneView | null = null,
  ): Piece[] {
    const pieces: Piece[] = [];
    let current = new Map(formats);
    let tattrs: Attrs | null = null;
    let tsig = '';
    let wrappers: WrapperValue[] = [];
    const snapshot = () => {
      if (tattrs === null) {
        tattrs = {};
        const all: Attrs = {};
        current.forEach((v, k) => {
          all[k] = v;
          if (!k.startsWith(WRAPPER_PREFIX)) {
            tattrs![k] = v;
          }
        });
        tsig = stableStringify(tattrs);
        wrappers = wrappersFromAttrs(all, this.isKnownWrapper);
      }
    };
    // With moves, the walk enters the ranges inline records show in place.
    const walk = zv === null ? null : zv.copy();
    const y = start === null ? null : (start.parent as YNode);
    let prev: Item | null = null;
    for (
      let it =
        start === stop
          ? null
          : walk === null
            ? start
            : enterZone(walk, y!, start, stop);
      it !== null && (walk !== null || it !== stop);
      prev = it, it = walk === null ? it.right : stepZone(walk, y!, it, stop)
    ) {
      if (walk !== null && (prev === null ? it !== start : it !== prev.right)) {
        current = formatsAfterItem(y!, it.left);
        tattrs = null;
      }
      if (it.deleted) {
        continue;
      }
      const content = it.content;
      if (content instanceof ContentFormat) {
        if (content.value === null) {
          current.delete(content.key);
        } else {
          current.set(content.key, content.value);
        }
        tattrs = null;
        continue;
      }
      if (!it.countable || (walk !== null && walk.foreign(it))) {
        continue;
      }
      snapshot();
      if (content instanceof ContentString) {
        const parts = content.str.split('\n');
        parts.forEach((part, i) => {
          if (i > 0) {
            pieces.push({kind: 'br', tattrs: tattrs!, wrappers});
          }
          for (const run of tabRuns(part, tattrs!, tsig)) {
            const last = pieces[pieces.length - 1];
            if (
              last !== undefined &&
              last.kind === 'text' &&
              last.tsig === run.tsig &&
              sameWrappers(last.wrappers, wrappers)
            ) {
              last.text += run.text;
            } else {
              pieces.push({
                kind: 'text',
                tattrs: run.tattrs,
                text: run.text,
                tsig: run.tsig,
                wrappers,
              });
            }
          }
        });
      } else if (content instanceof ContentType) {
        const name = (content.type.name as string) || '';
        if (name.startsWith(INLINE_PREFIX) && !isBlockNodeType(content.type)) {
          pieces.push({kind: 'node', wrappers, y: content.type});
        }
      }
    }
    this.lastFormats = current;
    return pieces;
  }

  /**
   * Lexical inline nodes for the content between two items, reusing the
   * nodes currently under `el` (and `extraPool`) where possible.
   */
  $readInline(
    start: Item | null,
    stop: Item | null,
    formats: Formats,
    el: ElementNode | null,
    extraPool?: LexicalNode[],
    zv: ZoneView | null = null,
  ): LexicalNode[] {
    const state = this.state;
    // Whether `el` (a list item) holds a nested group first before the read:
    // the wrappers built below can move that child into a link before `el`'s
    // children are set (see the end).
    const firstWasGroup = el !== null && $isGroupNode(el.getFirstChild());
    const texts: TextNode[] = [];
    const brs: LexicalNode[] = [];
    const wrappersPool = new Map<string, ElementNode[]>();
    const collect = (nodes: LexicalNode[]) => {
      for (const n of nodes) {
        if ($isTextNode(n)) {
          texts.push(n);
        } else if ($isLineBreakNode(n)) {
          brs.push(n);
        } else if (
          $isElementNode(n) &&
          n.isInline() &&
          getWrapperSpec(klassOf(n)) !== null
        ) {
          let list = wrappersPool.get(n.getType());
          if (list === undefined) {
            list = [];
            wrappersPool.set(n.getType(), list);
          }
          list.push(n);
          collect(n.getChildren());
        } else if ($isParagraphNode(n) && !state.yByKey.has(n.getKey())) {
          // A paragraph a read wrapped around inline content in a shadow
          // root (see $inShadowRoot).
          shown.push(n);
          collect(n.getChildren());
        }
      }
    };
    const shown: ElementNode[] = [];
    if (el !== null) {
      collect(el.getChildren());
    }
    if (extraPool !== undefined) {
      collect(extraPool);
    }
    const bySegment = new Map<string, TextNode>();
    for (const t of texts) {
      const s = state.segments.get(t.getKey());
      if (s !== undefined) {
        bySegment.set(s, t);
      }
    }
    const usedTexts = new Set<TextNode>();
    let textPtr = 0;
    const takeText = (
      type: string,
      segment: string | null,
    ): TextNode | null => {
      if (segment !== null) {
        const t = bySegment.get(segment);
        if (t !== undefined && !usedTexts.has(t) && t.getType() === type) {
          usedTexts.add(t);
          return t;
        }
        return null;
      }
      while (textPtr < texts.length) {
        const t = texts[textPtr++];
        if (
          !usedTexts.has(t) &&
          t.getType() === type &&
          !state.segments.has(t.getKey()) &&
          !(composedPlaced && t.getKey() === composedKey)
        ) {
          usedTexts.add(t);
          return t;
        }
      }
      return null;
    };
    const pieces = this.$pieces(start, stop, formats, zv);
    // The node being composed (IME) keeps its key and its text: content a
    // remote change puts next to it (a join) goes into nodes of its own, so
    // the browser's composition stays in its DOM text node (Lexical does not
    // merge text into the composed node; they merge when it ends).
    const composedKey = state.editor._compositionKey;
    const found =
      composedKey === null
        ? undefined
        : texts.find(t => t.getKey() === composedKey);
    const composed = found === undefined ? null : found;
    let composedPlaced = false;
    if (composed !== null) {
      const ct = composed.getTextContent();
      for (let k = 0; ct !== '' && k < pieces.length; k++) {
        const piece = pieces[k];
        if (
          piece.kind !== 'text' ||
          (piece.tattrs[TYPE_KEY] ?? 'text') !== composed.getType()
        ) {
          continue;
        }
        const at = piece.text.indexOf(ct);
        if (at < 0) {
          continue;
        }
        const parts: Piece[] = [];
        if (at > 0) {
          parts.push({...piece, text: piece.text.slice(0, at)});
        }
        parts.push({...piece, composed: true, text: ct});
        if (at + ct.length < piece.text.length) {
          parts.push({...piece, text: piece.text.slice(at + ct.length)});
        }
        pieces.splice(k, 1, ...parts);
        composedPlaced = true;
        break;
      }
    }
    // Reading nested inline nodes reads their own content: keep this
    // sequence's end formats for the caller.
    const endFormats = this.lastFormats;
    const top: LexicalNode[] = [];
    type Frame = {
      value: WrapperValue;
      node: ElementNode;
      children: LexicalNode[];
    };
    const stack: Frame[] = [];
    const finish = (frame: Frame) => {
      this.$setChildren(frame.node, frame.children);
    };
    const runLength = (from: number, sig: string) => {
      let n = 0;
      for (let k = from; k < pieces.length; k++) {
        if (!pieces[k].wrappers.some(w => w.sig === sig)) {
          break;
        }
        n++;
      }
      return n;
    };
    for (let k = 0; k < pieces.length; k++) {
      const piece = pieces[k];
      const want = piece.wrappers;
      // Close frames whose wrapper this piece does not have.
      let keepDepth = 0;
      while (
        keepDepth < stack.length &&
        want.some(w => w.sig === stack[keepDepth].value.sig)
      ) {
        keepDepth++;
      }
      while (stack.length > keepDepth) {
        finish(stack.pop()!);
      }
      // Open missing wrappers, longest run outermost.
      const missing = want
        .filter(w => !stack.some(f => f.value.sig === w.sig))
        .map(w => ({len: runLength(k, w.sig), w}))
        .sort(
          (a, b) =>
            b.len - a.len ||
            (a.w.type < b.w.type ? -1 : a.w.type > b.w.type ? 1 : 0),
        );
      for (const {w} of missing) {
        const node = this.$wrapperNode(w, wrappersPool);
        (stack.length > 0 ? stack[stack.length - 1].children : top).push(node);
        stack.push({children: [], node, value: w});
      }
      const target = stack.length > 0 ? stack[stack.length - 1].children : top;
      if (piece.kind === 'text') {
        let json = textJSONFromAttrs(piece.text, piece.tattrs);
        if (!state.editor._nodes.has(json.type as string)) {
          state.unknownTypes.add(json.type as string);
          json = {...json, type: 'text'};
        }
        json = joinSetMembersInJSON(json, state.editor);
        const segment =
          typeof piece.tattrs[SEGMENT_KEY] === 'string'
            ? (piece.tattrs[SEGMENT_KEY] as string)
            : null;
        let node: TextNode | null;
        if (piece.composed === true && composed !== null) {
          usedTexts.add(composed);
          node = composed;
        } else {
          node = takeText(json.type as string, segment);
        }
        if (node !== null) {
          const currentSig = stableStringify($textAttrs(node, segment));
          if (currentSig !== piece.tsig) {
            node = $applyJSON(node, json);
          }
          if (node.getTextContent() !== piece.text) {
            node = node.setTextContent(piece.text);
          }
        } else {
          node = $parseSerializedNode(
            json as unknown as SerializedLexicalNode,
          ) as TextNode;
          if (segment !== null) {
            state.setSegment(node.getKey(), segment);
          }
        }
        target.push(node);
      } else if (piece.kind === 'br') {
        let br = brs.shift() || $createLineBreakNode();
        const brState = lineBreakStateFromAttrs(piece.tattrs);
        if (
          stableStringify(lineBreakStateFromAttrs($lineBreakAttrs(br, {}))) !==
          stableStringify(brState)
        ) {
          br = br.getWritable();
          const info = state.editor._nodes.get(br.getType());
          $getWritableNodeState(br).updateFromJSON(
            joinSetMembers(
              brState,
              info && info.sharedNodeState.sharedConfigMap,
            ),
          );
        }
        target.push(br);
      } else {
        let node = this.$storedNode(piece.y);
        if (node === null) {
          node = this.$createStored(piece.y);
        }
        if (
          node !== null &&
          state.blockIds !== null &&
          piece.y.getAttr(STATE_PREFIX + blockIdState.key) === undefined
        ) {
          this.inlineStored.add(node.getKey());
        }
        // An inline element that cannot be empty (a mark whose text peers
        // deleted concurrently) is not shown, as Lexical would remove it.
        if (
          node !== null &&
          !(
            $isElementNode(node) &&
            !node.canBeEmpty() &&
            node.getChildrenSize() === 0
          )
        ) {
          target.push(node);
        }
      }
    }
    while (stack.length > 0) {
      finish(stack.pop()!);
    }
    this.lastFormats = endFormats;
    // An item that starts or stops holding a nested group first (a link put
    // around its nested list) is numbered differently by its group.
    const holder = el === null ? null : el.getParent();
    if (
      holder !== null &&
      $isGroupNode(holder) &&
      firstWasGroup !== $isGroupNode(top.length > 0 ? top[0] : null)
    ) {
      state.refresh.add(holder.getKey());
    }
    return el !== null && el.isShadowRoot() ? $inShadowRoot(top, shown) : top;
  }

  private $wrapperNode(
    w: WrapperValue,
    pool: Map<string, ElementNode[]>,
  ): ElementNode {
    const node = this.$wrapperNodeFor(w, pool);
    if (w.instance !== null) {
      this.state.setSegment(node.getKey(), w.instance);
    } else {
      this.state.segments.delete(node.getKey());
    }
    return node;
  }

  private $wrapperNodeFor(
    w: WrapperValue,
    pool: Map<string, ElementNode[]>,
  ): ElementNode {
    const list = pool.get(w.type);
    const reused = list !== undefined ? list.shift() : undefined;
    if (reused !== undefined) {
      const own: Attrs = {};
      $wrapperAttrs(reused, own);
      const current = wrappersFromAttrs(own, () => true)[0];
      if (
        current === undefined ||
        stableStringify(current.json) !== stableStringify(w.json)
      ) {
        const spec = getWrapperSpec(klassOf(reused))!;
        const json = $schemaJSON(reused);
        for (const f of spec.fields) {
          delete json[f];
        }
        delete json.textFormat;
        delete json.textStyle;
        Object.assign(json, w.json);
        const writable = reused.updateFromJSON(
          json as Parameters<ElementNode['updateFromJSON']>[0],
        );
        $setTextFields(writable, w.json);
        $setStateInOrder(writable, (w.json.$ as Attrs) || {});
        return writable;
      }
      return reused;
    }
    return $parseSerializedNode({
      ...w.json,
      children: [],
    } as unknown as SerializedLexicalNode) as ElementNode;
  }

  /** Make `el`'s children exactly `children`, keeping unchanged ends. */
  $setChildren(el: ElementNode, children: LexicalNode[]): void {
    const prev = el.getChildren();
    let left = 0;
    const max = Math.min(prev.length, children.length);
    while (left < max && prev[left].getKey() === children[left].getKey()) {
      left++;
    }
    let right = 0;
    while (
      right < max - left &&
      prev[prev.length - 1 - right].getKey() ===
        children[children.length - 1 - right].getKey()
    ) {
      right++;
    }
    if (left === prev.length && left === children.length) {
      return;
    }
    const middle = children.slice(left, children.length - right);
    const writable = el.getWritable();
    // Remote reads skip transforms: a group whose children change (or lose
    // a child to another element) recomputes its derived fields (list item
    // values) in the refresh that follows the read.
    const isGroup = (n: LexicalNode | null) =>
      $isElementNode(n) && getGroupSpec(klassOf(n)) !== null;
    if (isGroup(el)) {
      this.state.refresh.add(el.getKey());
    }
    for (const c of middle) {
      const parent = c.getParent();
      if (parent !== null && !parent.is(el) && isGroup(parent)) {
        this.state.refresh.add(parent.getKey());
      }
    }
    // An item whose first child changes between a nested group and other
    // content stops or starts being a wrapper item, which its group's
    // numbering counts differently (as a full read refreshes it).
    const holder = el.getParent();
    if (
      isGroup(holder) &&
      isGroup(prev.length > 0 ? prev[0] : null) !==
        isGroup(children.length > 0 ? children[0] : null)
    ) {
      this.state.refresh.add(holder!.getKey());
    }
    // A reused node can hold `el` (concurrent edits moved a list into the
    // line of an item that list held): take `el` out first, or the tree
    // would get a cycle. Its own container's read places it again.
    if (middle.some($isElementNode)) {
      const ancestors = new Set<NodeKey>();
      for (let p = el.getParent(); p !== null; p = p.getParent()) {
        ancestors.add(p.getKey());
      }
      if (middle.some(c => ancestors.has(c.getKey()))) {
        writable.remove(true);
      }
    }
    const removeCount = prev.length - left - right;
    if (middle.length === removeCount && middle.length >= 64) {
      // A reorder of many children (a long move shown by a record): move
      // only the children out of order rather than splice them all.
      const pos = new Map<NodeKey, number>();
      for (let k = left; k < prev.length - right; k++) {
        pos.set(prev[k].getKey(), k - left);
      }
      const pairs: [number, number][] = [];
      let permutation = true;
      middle.forEach((c, i) => {
        const p = pos.get(c.getKey());
        if (p === undefined) {
          permutation = false;
        } else {
          pairs.push([i, p]);
        }
      });
      if (permutation) {
        const keep = new Set(longestIncreasing(pairs).map(([i]) => i));
        let before: LexicalNode | null = left > 0 ? prev[left - 1] : null;
        middle.forEach((c, i) => {
          if (!keep.has(i)) {
            if (before === null) {
              const first = el.getFirstChild();
              if (first === null) {
                el.append(c);
              } else if (!first.is(c)) {
                first.insertBefore(c);
              }
            } else {
              before.insertAfter(c);
            }
          }
          before = c;
        });
        return;
      }
    }
    writable.splice(left, removeCount, middle);
  }

  private $repairSelection(): void {
    const selection = $getSelection();
    if ($isRangeSelection(selection)) {
      const a = $getNodeByKey(selection.anchor.key);
      const f = $getNodeByKey(selection.focus.key);
      if (a === null || f === null || !a.isAttached() || !f.isAttached()) {
        $setSelection(null);
      }
    }
  }
}

type GroupItemInfo = {
  gkey: Attrs;
  gtype: string;
  level: number;
  outer: Attrs[] | null;
  spec: GroupSpec;
};

/**
 * A reused node about to take `kids` as children must not be inside one of
 * them (an old wrapper holding the reused group): detach it first, or the
 * tree would get a cycle.
 */
function $detachFromKids(node: ElementNode, kids: LexicalNode[]): void {
  for (const k of kids) {
    if ($isElementNode(k) && k.isParentOf(node)) {
      node.remove(true);
      return;
    }
  }
}

/** Fields that tie a node into the tree, never copied between nodes. */
const TREE_FIELDS = new Set([
  '__key',
  '__parent',
  '__prev',
  '__next',
  '__first',
  '__last',
  '__size',
  '__type',
  '__state',
  '__slots',
  '__slotHost',
  '__cachedText',
]);

/**
 * Apply serialized fields to a node. A class without a generated
 * updateFromJSON (a hand-written importJSON that reads fields of its own)
 * drops those fields in updateFromJSON: then the fields are taken from a
 * node its importJSON builds.
 */
/**
 * Set a node's NodeState in the order of `state` (sorted by the reader):
 * NodeState keeps its keys in the order they were first set, so a node that
 * gained a key later would serialize its keys in another order than a peer
 * that read them at once.
 */
function $setStateInOrder(node: LexicalNode, state: Attrs): void {
  const current = node.__state;
  if (current !== undefined) {
    const json = current.toJSON() as Attrs;
    const nested = (json.$ as Attrs | undefined) || {};
    const have = Object.keys(nested).filter(k => k in state);
    const want = Object.keys(state).filter(k => k in nested);
    if (have.join('\u0000') !== want.join('\u0000')) {
      node.getWritable().__state = undefined;
    }
  }
  $getWritableNodeState(node).updateFromJSON(state);
}

function $applyJSON<T extends LexicalNode>(node: T, json: Attrs): T {
  if (json.$ !== undefined && node.__state !== undefined) {
    $setStateInOrder(node, json.$ as Attrs);
  }
  const w = node.updateFromJSON(
    json as Parameters<LexicalNode['updateFromJSON']>[0],
  ) as T;
  const after = w.exportJSON() as unknown as Attrs;
  let same = true;
  for (const k in json) {
    if (
      k !== 'children' &&
      k !== 'version' &&
      k !== '$' &&
      k !== 'textFormat' &&
      k !== 'textStyle' &&
      stableStringify(after[k]) !== stableStringify(json[k])
    ) {
      same = false;
      break;
    }
  }
  if (same) {
    return w;
  }
  const tmp = $parseSerializedNode({
    ...json,
    ...($isElementNode(w) ? {children: []} : {}),
  } as unknown as SerializedLexicalNode) as unknown as Record<string, unknown>;
  const target = w.getWritable() as unknown as Record<string, unknown>;
  for (const k of Object.keys(tmp)) {
    if (k.startsWith('__') && !TREE_FIELDS.has(k)) {
      target[k] = tmp[k];
    }
  }
  return target as unknown as T;
}

/**
 * The runs of `text` and the attributes each is read with. A tab's type
 * (`t: 'tab'`) and segment key apply to its `\t` only: other text inside
 * a tab's format range (left open there when the client that wrote the tab
 * removed it, while another client's content written inside it stays) is
 * read as plain text, never as tabs.
 */
function tabRuns(
  text: string,
  tattrs: Attrs,
  tsig: string,
): {text: string; tattrs: Attrs; tsig: string}[] {
  if (text.length === 0) {
    return [];
  }
  if (decodeFormatValue(tattrs[TYPE_KEY]) !== 'tab' || /^\t+$/.test(text)) {
    return [{tattrs, text, tsig}];
  }
  const plain: Attrs = {...tattrs};
  delete plain[TYPE_KEY];
  delete plain[SEGMENT_KEY];
  const plainSig = stableStringify(plain);
  return (text.match(/\t+|[^\t]+/g) || []).map(run =>
    run[0] === '\t'
      ? {tattrs, text: run, tsig}
      : {tattrs: plain, text: run, tsig: plainSig},
  );
}

function groupSig(attrs: Attrs, group: GroupItemInfo | null): string {
  if (group === null) {
    return '';
  }
  return writerGroupSig(
    attrs[TYPE_KEY] as string,
    groupKeySig({[GROUP_KEY]: group.gtype, ...group.gkey}, group.outer || []),
    group.level,
  );
}

/** Group attributes (g:<field>) from group fields. */
function keyFromFields(fields: Attrs): Attrs {
  const out: Attrs = {};
  for (const f in fields) {
    if (!isUnsafeKey(f) && f !== WRAPPER_FIELDS_KEY) {
      out[GROUP_FIELD_PREFIX + f] = fields[f];
    }
  }
  return out;
}

/**
 * Set the start formats of the units after the first of `from` from the
 * shared items, until they agree again past the last of `from`; returns the
 * units whose start changed (they must be read again).
 */
function recomputeUnitStarts(cs: CS, from: Unit[]): Unit[] {
  const units = cs.units;
  const changed: Unit[] = [];
  const index = new Map<Unit, number>();
  units.forEach((u, i) => index.set(u, i));
  let first = units.length;
  let last = -1;
  for (const u of from) {
    const i = index.get(u);
    if (i !== undefined) {
      first = Math.min(first, i);
      last = Math.max(last, i);
    }
  }
  if (first >= units.length) {
    return changed;
  }
  const formats = new Map<string, unknown>(units[first].start || EMPTY_FORMATS);
  const set = (u: Unit): boolean => {
    const next = formats.size > 0 ? new Map(formats) : null;
    const differs = !sameFormats(
      u.start || EMPTY_FORMATS,
      next || EMPTY_FORMATS,
    );
    if (differs) {
      changed.push(u);
    }
    u.start = next;
    return differs;
  };
  let k = first;
  let left: Item | null = null;
  for (let m = first - 1; m >= 0 && left === null; m--) {
    left = units[m].end;
  }
  for (
    let it = left === null ? cs.y._start : left.right;
    it !== null && k < units.length;
    it = it.right
  ) {
    if (!it.deleted && it.content instanceof ContentFormat) {
      const {key, value} = it.content;
      if (value === null) {
        formats.delete(key);
      } else {
        formats.set(key, value);
      }
    }
    // Text without an end item ends where the next unit (a block node)
    // starts.
    if (
      units[k].end === null &&
      k + 1 < units.length &&
      it === units[k + 1].end
    ) {
      k++;
      if (!set(units[k]) && k > last) {
        break;
      }
    }
    if (it === units[k].end) {
      k++;
      if (k < units.length && !set(units[k]) && k > last) {
        break;
      }
    }
  }
  return changed;
}

/** The formats in effect right after unit `k` (empty before the first). */
function formatsAfterUnit(units: Unit[], k: number): Formats {
  if (k < 0) {
    return EMPTY_FORMATS;
  }
  const u = units[k];
  const formats = new Map(u.start || EMPTY_FORMATS);
  if (u.end === null) {
    return formats;
  }
  let left: Item | null = null;
  for (let m = k - 1; m >= 0 && left === null; m--) {
    const e = units[m].end;
    if (e !== null && !e.deleted) {
      left = e;
    }
  }
  for (
    let it: Item | null = left === null ? u.cs.y._start : left.right;
    it !== null;
    it = it.right
  ) {
    if (!it.deleted && it.content instanceof ContentFormat) {
      const {key, value} = it.content;
      if (value === null) {
        formats.delete(key);
      } else {
        formats.set(key, value);
      }
    }
    if (it === u.end) {
      break;
    }
  }
  return formats;
}

/**
 * The block id of a line without a marker (text that concurrent edits left
 * without one), the same on every client and on every read: `y`, the client
 * of its first character's Yjs item, `_` and that item's clock, in base 36,
 * and `_l` when that item is a node stored in the line (which derives its
 * own id from it, see storedDerivedId). A block id is 1 to 64 characters of
 * the base64url alphabet. A write that gives the line a marker stores the
 * id the line has, so it stays.
 */
function implicitBlockId(start: Item | null, stop: Item | null): string | null {
  for (let it = start; it !== null && it !== stop; it = it.right) {
    if (!it.deleted && it.countable) {
      return (
        derivedBlockId(it) + (it.content instanceof ContentType ? '_l' : '')
      );
    }
  }
  return null;
}

/**
 * Note the ids whose claimants an update changed beyond what its reads
 * noted as they went (see State#noteStoredId, Reader#noteDerived): a block
 * removed leaves the index, and the id it stored and the id it showed are
 * settled again (blocks that fell back because of it may show it now); a
 * block shown with another id than before the update has both settled (a
 * group whose first line changed, a line read again with the id it stores);
 * a changed block that holds an id another block claims too has it settled
 * (it may have moved past that block). Proportional to what the update
 * changed.
 */
export function $touchChanged(
  state: State,
  dirtyElements: ReadonlyMap<NodeKey, unknown> = state.editor._dirtyElements,
  dirtyLeaves: ReadonlySet<NodeKey> = state.editor._dirtyLeaves,
  before: ReadonlyMap<NodeKey, LexicalNode> = state.editor._editorState
    ._nodeMap,
  touch: (id: string) => void = id => state.touchedIds.add(id),
): void {
  const seen = new Set<NodeKey>();
  const removed = (key: NodeKey, prev: LexicalNode | undefined) => {
    const stored = state.storedIdOf.get(key);
    state.noteStoredId(key, undefined);
    const was =
      prev === undefined
        ? undefined
        : $getState(prev, blockIdState, NODE_STATE_DIRECT);
    for (const id of [stored, was]) {
      if (typeof id === 'string') {
        touch(id);
      }
    }
    // What it held went with it (Lexical marks only the node removed).
    if ($isElementNode(prev)) {
      for (let c = prev.__first; c !== null; ) {
        const child = before.get(c);
        if (child === undefined) {
          break;
        }
        if (!seen.has(c)) {
          const now = $getNodeByKey(c);
          // One placed elsewhere is changed (see visit), not removed.
          if (now === null || !now.isAttached()) {
            seen.add(c);
            removed(c, child);
          }
        }
        c = child.__next;
      }
    }
  };
  const visit = (key: NodeKey) => {
    if (seen.has(key)) {
      return;
    }
    seen.add(key);
    const node = $getNodeByKey(key);
    const prev = before.get(key);
    if ($isTextNode(node) || (node === null && $isTextNode(prev))) {
      return;
    }
    if (node === null || !node.isAttached()) {
      removed(key, prev);
      return;
    }
    const was =
      prev === undefined
        ? undefined
        : $getState(prev, blockIdState, NODE_STATE_DIRECT);
    const now = $getState(node, blockIdState);
    if (prev !== undefined && was !== now) {
      for (const id of [was, now]) {
        if (typeof id === 'string') {
          touch(id);
        }
      }
    }
    // Moved (or new), with what it holds: it may have moved past another
    // holder of an id it claims. Typing in a block does not move it.
    if (
      prev === undefined ||
      prev.__parent !== node.__parent ||
      prev.__prev !== node.__prev ||
      prev.__next !== node.__next
    ) {
      const holds = (n: LexicalNode) => {
        for (const id of [
          $getState(n, blockIdState),
          state.storedIdOf.get(n.getKey()),
        ]) {
          if (typeof id === 'string' && state.repeatedIds.has(id)) {
            touch(id);
          }
        }
        if ($isElementNode(n)) {
          for (const c of n.getChildren()) {
            holds(c);
          }
        }
      };
      holds(node);
    }
  };
  for (const key of dirtyElements.keys()) {
    visit(key);
  }
  for (const key of dirtyLeaves) {
    visit(key);
  }
}

/**
 * The block id stored for a node a read gave one (see State#storedIdOf), as
 * the document holds it now: a line's marker, a stored node's attributes, a
 * top-level group's first item's marker.
 */
export function $storedIdNow(state: State, node: LexicalNode): unknown {
  const key = node.getKey();
  const k = STATE_PREFIX + blockIdState.key;
  const unit = state.unitByKey.get(key);
  if (unit !== undefined && unit.key === key) {
    return unit.end === null ? undefined : typeOf(unit.end).getAttr(k);
  }
  const isGroup = $isElementNode(node) && getGroupSpec(klassOf(node)) !== null;
  const y = state.yByKey.get(key);
  if (y !== undefined) {
    // A stored node (a list stored as a node too): its attributes.
    return y.getAttr(k);
  }
  if (!$isElementNode(node)) {
    return state.storedIdOf.get(key);
  }
  // A group's id is stored with its level's key by its first item, a
  // wrapper item's in its nested items' outer keys (see $groupChildren):
  // read from the first line under it.
  const first = node.getFirstChild();
  if (
    !isGroup &&
    !($isElementNode(first) && getGroupSpec(klassOf(first)) !== null)
  ) {
    return state.storedIdOf.get(key);
  }
  let groups = 0;
  let line: Unit | undefined;
  for (let n: LexicalNode | null = first; n !== null; ) {
    const u = state.unitByKey.get(n.getKey());
    if (u !== undefined && u.key === n.getKey()) {
      line = u;
      break;
    }
    if (!$isElementNode(n)) {
      break;
    }
    if (getGroupSpec(klassOf(n)) !== null) {
      groups++;
    }
    n = n.getFirstChild();
  }
  if (line === undefined || line.end === null) {
    return state.storedIdOf.get(key);
  }
  const attrs = typeOf(line.end).getAttrs() as Attrs;
  // Only a marker that puts its line in a group records group ids (see
  // Reader#$groupOf): an item whose group key concurrent edits removed is
  // read in a group of its own class's, which stores none.
  const nodes = state.editor._nodes;
  const g = attrs[GROUP_KEY];
  const ginfo = typeof g === 'string' ? nodes.get(g) : undefined;
  const spec = ginfo === undefined ? null : getGroupSpec(ginfo.klass);
  const t = attrs[TYPE_KEY];
  const info = nodes.get(typeof t === 'string' ? t : 'paragraph');
  if (spec === null || info === undefined || !spec.items.includes(info.klass)) {
    return undefined;
  }
  const lv = attrs[LEVEL_KEY];
  const level = typeof lv === 'number' && Number.isInteger(lv) ? lv : 0;
  const idIn = (st: unknown): unknown =>
    st !== null && typeof st === 'object' && !Array.isArray(st)
      ? (st as Attrs)[blockIdState.key]
      : undefined;
  if (isGroup && groups === 0) {
    return idIn(attrs[GROUP_FIELD_PREFIX + '$']);
  }
  const at = level - groups;
  const outer = attrs[OUTER_KEY];
  const entry =
    Array.isArray(outer) && outer.length === level && at >= 0
      ? outer[at]
      : undefined;
  if (entry === null || typeof entry !== 'object' || Array.isArray(entry)) {
    return state.storedIdOf.get(key);
  }
  if (isGroup) {
    return idIn((entry as Attrs).$);
  }
  const w = (entry as Attrs)[WRAPPER_FIELDS_KEY];
  return w !== null && typeof w === 'object' && !Array.isArray(w)
    ? idIn((w as Attrs).$)
    : undefined;
}

/**
 * Whether a node is inside a named slot. Blocks there that repeat an id are
 * left to BlockIdExtension's naming (written), as their order in the
 * document is not a property every reader computes the same way.
 */
function $inNamedSlot(n: LexicalNode): boolean {
  let x: LexicalNode = n;
  for (let p = x.getParent(); p !== null; p = x.getParent()) {
    x = p;
  }
  return !$isRootNode(x);
}

/**
 * The block id derived from a marker or a stored node, the same on every
 * client and every read (see implicitBlockId): `y`, the item's client, `_`
 * and its clock, in base 36.
 */
function derivedBlockId(item: Item): string {
  return 'y' + item.id.client.toString(36) + '_' + item.id.clock.toString(36);
}

/**
 * The derived id of a stored node (see derivedBlockId), from its own item;
 * a list's ends in `_g` (a line without a marker that starts with it
 * derives its id from that item too, see implicitBlockId).
 */
function storedDerivedId(node: LexicalNode, item: Item): string {
  return derivedBlockId(item) + ($isGroupNode(node) ? groupSuffix(0) : '');
}

/** Whether a node is a group (a list). */
function $isGroupNode(n: LexicalNode | null): n is ElementNode {
  return $isElementNode(n) && getGroupSpec(klassOf(n)) !== null;
}

/** The suffix of a wrapper item's derived id (see Reader#$derivedIdOf). */
function wrapperSuffix(level: number): string {
  return level === 0 ? '_w' : '_w' + level;
}

/** The suffix of a group's derived id (see Reader#$derivedIdOf). */
function groupSuffix(level: number): string {
  return level === 0 ? '_g' : '_g' + level;
}

/**
 * The derived id of a line without a marker (see implicitBlockId): its
 * content runs from the end of the unit before it to the node after it.
 */
function implicitIdOf(unit: Unit): string | null {
  const units = unit.cs.units;
  const i = units.indexOf(unit);
  if (i < 0) {
    return null;
  }
  const prev = i > 0 ? units[i - 1].end : null;
  if (i > 0 && prev === null) {
    return null;
  }
  const next = i + 1 < units.length ? units[i + 1].end : null;
  return implicitBlockId(prev === null ? unit.cs.y._start : prev.right, next);
}

/** One settling of block ids (see Reader#$settleIds): what it computed. */
type SettlePass = {
  readonly shown: Map<NodeKey, string | null>;
  readonly claimants: Map<string, LexicalNode[]>;
  readonly paths: Map<NodeKey, number[]>;
  /** Index within its parent, for every child of a parent walked once. */
  readonly index: Map<NodeKey, number>;
};

function newSettlePass(): SettlePass {
  return {
    claimants: new Map(),
    index: new Map(),
    paths: new Map(),
    shown: new Map(),
  };
}

/**
 * A node's position in the document (see comparePaths). Each parent's
 * children are counted once per pass, so placing many blocks of one parent
 * costs one walk of it, not one per block.
 */
function $pathOf(n: LexicalNode, pass: SettlePass): number[] {
  let path = pass.paths.get(n.getKey());
  if (path === undefined) {
    path = [];
    for (let x: LexicalNode | null = n; x !== null && !$isRootNode(x); ) {
      const parent: ElementNode | null = x.getParent();
      let i = pass.index.get(x.getKey());
      if (i === undefined && parent !== null) {
        let k = 0;
        for (
          let c: LexicalNode | null = parent.getFirstChild();
          c !== null;
          c = c.getNextSibling()
        ) {
          pass.index.set(c.getKey(), k++);
        }
        i = pass.index.get(x.getKey());
      }
      path.push(i === undefined ? x.getIndexWithinParent() : i);
      x = parent;
    }
    path.reverse();
    pass.paths.set(n.getKey(), path);
  }
  return path;
}

/** Document order of two positions (see $pathOf). */
function comparePaths(pa: number[], pb: number[]): number {
  for (let i = 0; i < Math.min(pa.length, pb.length); i++) {
    if (pa[i] !== pb[i]) {
      return pa[i] - pb[i];
    }
  }
  return pa.length - pb.length;
}

/** A marker's attributes; a marker without a type is a paragraph's. */
function markerAttrs(y: YNode): Attrs {
  const attrs = y.getAttrs() as Attrs;
  if (typeof attrs[TYPE_KEY] !== 'string') {
    attrs[TYPE_KEY] = 'paragraph';
  }
  return attrs;
}

function isLineFieldKey(
  k: string,
  fields: ReadonlySet<string>,
  derived: ReadonlySet<string> | null,
): boolean {
  if (k.startsWith(STATE_PREFIX)) {
    return true;
  }
  if (k.startsWith(FIELD_PREFIX)) {
    const f = k.slice(FIELD_PREFIX.length);
    return (
      fields.has(f) && (derived === null || !derived.has(f)) && !isUnsafeKey(f)
    );
  }
  return false;
}

function lineJSON(
  attrs: Attrs,
  derived: ReadonlySet<string> | null,
  type: string,
): Attrs {
  const info = {fields: new Set<string>()};
  const json: Attrs = {children: [], type, version: 1};
  const state: Attrs = {};
  let hasState = false;
  for (const k of Object.keys(attrs).sort()) {
    if (k.startsWith(STATE_PREFIX)) {
      const f = k.slice(STATE_PREFIX.length);
      if (!isUnsafeKey(f)) {
        state[f] = attrs[k];
        hasState = true;
      }
    } else if (k.startsWith(FIELD_PREFIX)) {
      const f = k.slice(FIELD_PREFIX.length);
      if (!isUnsafeKey(f) && (derived === null || !derived.has(f))) {
        json[f] = attrs[k];
        info.fields.add(f);
      }
    }
  }
  if (hasState) {
    json.$ = state;
  }
  return json;
}

/** Group and level nodes of the tops of `units`, to reuse. */
function $newPool(units: Unit[], state: State): Pool {
  const pool: Pool = {
    groups: new Map(),
    levelKeys: new Set(),
    levels: [],
    lines: new Set(),
  };
  const seenTops = new Set<NodeKey>();
  for (const u of units) {
    if (u.sig !== '' && u.first !== null && !seenTops.has(u.first)) {
      seenTops.add(u.first);
      const top = $getNodeByKey(u.first);
      if ($isElementNode(top)) {
        collectPool(top, pool, state);
      }
    }
  }
  return pool;
}

/**
 * The children a read gives a line that is a shadow root (a quote that holds
 * paragraphs): each run of inline content in it (text a collaborator typed
 * into a paragraph that another moved into the quote, which lands next to
 * the moved paragraph) shown in a paragraph of its own, as a shadow root
 * holds only blocks. Every reader shows it so; the next local edit there
 * stores it. Reuses the paragraphs an earlier read made (`shown`), in order.
 */
function $inShadowRoot(
  children: LexicalNode[],
  shown: ElementNode[],
): LexicalNode[] {
  const out: LexicalNode[] = [];
  let run: LexicalNode[] = [];
  let k = 0;
  const flush = () => {
    if (run.length > 0) {
      const p = k < shown.length ? shown[k++] : $createParagraphNode();
      $detachFromKids(p, run);
      for (const c of p.getChildren()) {
        if (!run.includes(c)) {
          c.remove();
        }
      }
      p.splice(0, p.getChildrenSize(), run);
      out.push(p);
      run = [];
    }
  };
  for (const c of children) {
    if ($isElementNode(c) && !c.isInline()) {
      flush();
      out.push(c);
    } else {
      run.push(c);
    }
  }
  flush();
  return out;
}

/**
 * The group nodes (and level wrappers) under a group read before, for the
 * read to reuse. An item whose only child is a group stored as its own node
 * (a list inside the item's line) is a line, not a level of the group.
 */
function collectPool(node: ElementNode, pool: Pool, state: State): void {
  const type = node.getType();
  const spec = getGroupSpec(klassOf(node));
  if (spec !== null) {
    let list = pool.groups.get(type);
    if (list === undefined) {
      list = [];
      pool.groups.set(type, list);
    }
    list.push(node);
    for (const c of node.getChildren()) {
      if ($isElementNode(c)) {
        const first = c.getFirstChild();
        if (
          first !== null &&
          first === c.getLastChild() &&
          $isElementNode(first) &&
          klassOf(first) === spec.klass &&
          !state.yByKey.has(first.getKey())
        ) {
          pool.levels.push(c);
          pool.levelKeys.add(c.getKey());
          collectPool(first, pool, state);
        }
      }
    }
  }
}

function sameWrappers(a: WrapperValue[], b: WrapperValue[]): boolean {
  return (
    a === b || (a.length === b.length && a.every((w, i) => w.sig === b[i].sig))
  );
}

function sameFormats(a: Formats, b: Formats): boolean {
  if (a.size !== b.size) {
    return false;
  }
  for (const [k, v] of a) {
    if (stableStringify(b.get(k)) !== stableStringify(v)) {
      return false;
    }
  }
  return true;
}

/** Whether a container holds a live move record. */
function holdsMove(y: YNode): boolean {
  for (let it = y._start; it !== null; it = it.right) {
    if (!it.deleted && isMoveItem(it)) {
      return true;
    }
  }
  return false;
}

function isDeleted(y: YNode): boolean {
  for (let t: YNode | null = y; t !== null; t = t.parent) {
    if (t._item !== null && t._item.deleted) {
      return true;
    }
  }
  return false;
}
