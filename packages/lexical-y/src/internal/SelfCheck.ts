/**
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 */

import type {Writer} from './Write';

import {blockIdState} from '@lexical/extension';
import {ContentType, type Node as YNode} from '@y/y';
import {
  $getNodeByKey,
  $getRoot,
  $getSlot,
  $getSlotNames,
  $isElementNode,
  $parseSerializedNode,
  createEditor,
  type EditorState,
  ElementNode,
  type LexicalEditor,
  type LexicalNode,
  type NodeKey,
  type SerializedLexicalNode,
  TextNode,
} from 'lexical';

import {equalFormatValue} from './Cursor';
import {$pushInline, Atoms, readAtoms} from './Inline';
import {Reader} from './Read';
import {
  type Attrs,
  decodeFormatValue,
  equalValue,
  getContainerGroupSpec,
  INLINE_PREFIX,
  isOwnedTextKey,
  isSetStateConfig,
  MARKER,
  RUN_END,
  SET_MEMBER_SEPARATOR,
  stableStringify,
  STATE_PREFIX,
  TEXT_FORMAT_PREFIX,
  TYPE_KEY,
  WRAPPER_PREFIX,
} from './Schema';
import {
  type CS,
  EMPTY_FORMATS,
  lineStart,
  startItemAfter,
  State,
} from './State';

/**
 * Development self-check of a local write: every line the write touched is
 * read back from Yjs (characters, owned formats, child nodes, marker
 * attributes) and compared with the editor's content. Returns the
 * mismatches found (empty when the write is faithful).
 */
/**
 * The shared text without stored elements a reader does not show (an
 * element that cannot be empty, emptied by peers).
 */
function $shownText(writer: Writer, atoms: Atoms): string {
  let out = '';
  for (let i = 0; i < atoms.text.length; i++) {
    const sp = atoms.specials.get(i);
    if (
      sp !== undefined &&
      sp.kind === 'oldNode' &&
      sp.item.content instanceof ContentType
    ) {
      const y = sp.item.content.type as YNode;
      const name = typeof y.name === 'string' ? y.name : '';
      const info = name.startsWith(INLINE_PREFIX)
        ? writer.state.editor._nodes.get(name.slice(INLINE_PREFIX.length))
        : undefined;
      if (
        info !== undefined &&
        info.klass.prototype instanceof ElementNode &&
        !(info.klass.prototype as ElementNode).canBeEmpty.call(
          Object.create(info.klass.prototype),
        ) &&
        !hasLiveContent(y)
      ) {
        continue;
      }
    }
    out += atoms.text[i];
  }
  return out;
}

function hasLiveContent(y: YNode): boolean {
  for (let it = y._start; it !== null; it = it.right) {
    if (!it.deleted && it.countable) {
      return true;
    }
  }
  return false;
}

export function $checkWrite(writer: Writer): string[] {
  const problems: string[] = [];
  const isKnownWrapper = (type: string) => writer.state.editor._nodes.has(type);
  // A line written twice in one write (its container rewritten after it)
  // is checked as last written.
  const last = new Map<string, number>();
  writer.touched.forEach(({unit}, at) => {
    if (unit.key !== null) {
      last.set(unit.key, at);
    }
  });
  for (const [at, {unit, d}] of writer.touched.entries()) {
    if (unit.key !== null && last.get(unit.key) !== at) {
      continue;
    }
    const end = unit.end;
    if (end === null || end.deleted) {
      problems.push(`unit ${String(unit.key)} has no live end`);
      continue;
    }
    const name = (end.content as ContentType).type.name;
    if (name !== (d.kind === 'run' ? RUN_END : MARKER)) {
      problems.push(`unit ${String(unit.key)} ends with ${String(name)}`);
      continue;
    }
    const nodes =
      d.part !== undefined
        ? d.part
        : d.kind === 'line'
          ? (() => {
              const line = $getNodeByKey(d.key!);
              return $isElementNode(line)
                ? (line as ElementNode).getChildren()
                : null;
            })()
          : d.nodes;
    if (nodes === null) {
      continue;
    }
    const want = new Atoms();
    // What was written: no node gets a new segment key here (a node this
    // write did not rewrite keeps the key it was read with, or none, as the
    // reader shows it).
    const ctx = writer.$ctx();
    ctx.segments = {
      create: () => null,
      get: key => writer.state.segments.get(key),
    };
    $pushInline(want, nodes, ctx);
    const {left, zone} = lineStart(writer.state, end);
    const have = new Atoms();
    readAtoms(
      startItemAfter(writer.state.zonesOf(unit.cs.y), unit.cs.y, left, zone),
      end,
      unit.start || EMPTY_FORMATS,
      have,
      writer.state.view(unit.cs.y, zone),
    );
    if (want.text !== have.text && want.text !== $shownText(writer, have)) {
      problems.push(
        `line ${String(unit.key)}: text ${JSON.stringify(have.text)} != ${JSON.stringify(want.text)}`,
      );
      continue;
    }
    if (want.text !== have.text) {
      // Equal once stored elements the reader hides are left out.
      continue;
    }
    let ra = 0;
    let rb = 0;
    let lastKey = '';
    for (let i = 0; i < want.length; i++) {
      while (ra < want.runs.length && want.runs[ra].end <= i) {
        ra++;
      }
      while (rb < have.runs.length && have.runs[rb].end <= i) {
        rb++;
      }
      const a = ra < want.runs.length ? want.runs[ra].attrs : {};
      const b = rb < have.runs.length ? have.runs[rb].attrs : {};
      const isBreak = !want.specials.has(i) && want.text.charCodeAt(i) === 10;
      const wrappersOnly = want.specials.has(i) || isBreak;
      const key =
        ra + '/' + rb + '/' + (wrappersOnly ? 1 : 0) + (isBreak ? i : '');
      if (key === lastKey) {
        continue;
      }
      lastKey = key;
      for (const k of new Set([...Object.keys(a), ...Object.keys(b)])) {
        // A wrapper's textFormat/textStyle at a character: Lexical's
        // reconciler derives them from the wrapper's text (see
        // stripGroupText).
        const derivedText = !wrappersOnly && k.startsWith(WRAPPER_PREFIX);
        if (
          !wrappersOnly &&
          k.startsWith(TEXT_FORMAT_PREFIX) &&
          dropsFormats(writer.state, a)
        ) {
          // A text class that keeps no formats (a code highlight): the
          // reader shows none, whatever is stored.
          continue;
        }
        if (
          (!wrappersOnly ||
            k.startsWith(WRAPPER_PREFIX) ||
            (isBreak && k.startsWith(STATE_PREFIX))) &&
          isOwnedTextKey(k, isKnownWrapper) &&
          !equalFormatValue(
            withoutTextFields(a[k] ?? null, derivedText),
            withoutTextFields(b[k] ?? null, derivedText),
          )
        ) {
          problems.push(`line ${String(unit.key)}: format ${k} at ${i}`);
          i = want.length;
          break;
        }
      }
    }
    if (d.kind === 'line') {
      const marker = writer.$marker(d);
      const attrs = (end.content as ContentType).type.getAttrs() as Record<
        string,
        unknown
      >;
      for (const k in marker) {
        if (
          !equalValue(attrs[k], marker[k]) &&
          !writer.keepsStored(k, attrs[k], marker[k])
        ) {
          problems.push(`line ${String(unit.key)}: marker ${k}`);
        }
      }
    }
  }
  return problems;
}

/**
 * A node's JSON with its children and named slots, as exportJSON gives it.
 * Adjacent text nodes that differ only in their text are compared as one
 * (Lexical keeps them apart while one of them is being composed). `unstored`
 * are nodes whose NodeState is left out (see $runNodes).
 */
function $deepJSON(
  node: LexicalNode,
  unstored: ReadonlySet<NodeKey> | null = null,
): Attrs {
  const json = node.exportJSON() as unknown as Attrs;
  if (unstored !== null && unstored.has(node.getKey())) {
    delete json.$;
  }
  if ($isElementNode(node)) {
    const children: Attrs[] = [];
    for (const child of node.getChildren()) {
      const c = $deepJSON(child, unstored);
      const prev = children[children.length - 1];
      if (
        prev !== undefined &&
        typeof prev.text === 'string' &&
        typeof c.text === 'string' &&
        stableStringify({...prev, text: ''}) ===
          stableStringify({...c, text: ''})
      ) {
        children[children.length - 1] = {...prev, text: prev.text + c.text};
      } else {
        children.push(c);
      }
    }
    json.children = children;
  }
  const names = $getSlotNames(node);
  if (names.length > 0) {
    const slots: Attrs = {};
    for (const name of names) {
      const slot = $getSlot(node, name);
      if (slot !== null) {
        slots[name] = $deepJSON(slot, unstored);
      }
    }
    json.$slots = slots;
  }
  return json;
}

/**
 * The inline nodes held directly by a container that holds blocks (a run,
 * which only a writer without Lexical's normalization stores, and its author
 * normalizes): an update that follows a commit on every client (an
 * extension naming blocks) can give one a NodeState value, which it does not
 * write (that would insert formats, see Writer#followUp).
 */
function $runNodes(state: State): Set<NodeKey> {
  const keys = new Set<NodeKey>();
  for (const cs of state.csByKey.values()) {
    if (cs.kind !== 'b') {
      continue;
    }
    for (const u of cs.units) {
      if (u.kind !== 'run' || u.first === null) {
        continue;
      }
      for (
        let n: LexicalNode | null = $getNodeByKey(u.first);
        n !== null;
        n = n.getNextSibling()
      ) {
        keys.add(n.getKey());
        if (n.getKey() === u.last) {
          break;
        }
      }
    }
  }
  return keys;
}

/**
 * Remove the textFormat/textStyle of groups and of the items that hold a
 * nested group. Lexical's reconciler derives them from the first text it
 * renders under the element, when it reconciles it, so clients (and the
 * author, after its write) that reconcile different parts of a list derive
 * different values, as they do for a line with text (which Lexical does not
 * serialize them for). They are still stored, so that an edit that sets them
 * (formatting a selection that holds a list) reaches every client.
 */
function stripGroupText(
  json: unknown,
  groupTypes: ReadonlySet<string>,
): unknown {
  if (Array.isArray(json)) {
    return json.map(j => stripGroupText(j, groupTypes));
  }
  if (json !== null && typeof json === 'object') {
    const node = json as Attrs;
    const children = Array.isArray(node.children)
      ? (node.children as Attrs[])
      : null;
    const strip =
      groupTypes.has(node.type as string) ||
      (children !== null &&
        children.length > 0 &&
        groupTypes.has(children[0].type as string));
    const out: Attrs = {};
    for (const k in node) {
      if (!strip || (k !== 'textFormat' && k !== 'textStyle')) {
        out[k] =
          k === 'children' ? stripGroupText(node[k], groupTypes) : node[k];
      }
    }
    return out;
  }
  return json;
}

/** A wrapper's format value without its textFormat/textStyle (`strip`). */
function withoutTextFields(value: unknown, strip: boolean): unknown {
  if (!strip || value === null || typeof value !== 'object') {
    return value;
  }
  const out: Attrs = {...(value as Attrs)};
  delete out.textFormat;
  delete out.textStyle;
  return out;
}

/** Remove fields every client derives itself (list numbering). */
function stripDerived(json: unknown, derived: ReadonlySet<string>): unknown {
  if (Array.isArray(json)) {
    return json.map(j => stripDerived(j, derived));
  }
  if (json !== null && typeof json === 'object') {
    const out: Attrs = {};
    for (const k of Object.keys(json as Attrs).sort()) {
      if (!derived.has(k)) {
        out[k] = stripDerived((json as Attrs)[k], derived);
      }
    }
    return out;
  }
  return json;
}

function firstDifference(a: unknown, b: unknown, path: string): string | null {
  if (stableStringify(a) === stableStringify(b)) {
    return null;
  }
  if (Array.isArray(a) && Array.isArray(b) && a.length === b.length) {
    for (let i = 0; i < a.length; i++) {
      const d = firstDifference(a[i], b[i], `${path}[${i}]`);
      if (d !== null) {
        return d;
      }
    }
  }
  if (
    a !== null &&
    b !== null &&
    typeof a === 'object' &&
    typeof b === 'object' &&
    !Array.isArray(a) &&
    !Array.isArray(b)
  ) {
    const keys = new Set([...Object.keys(a), ...Object.keys(b)]);
    for (const k of [...keys].sort()) {
      const d = firstDifference(
        (a as Attrs)[k],
        (b as Attrs)[k],
        `${path}.${k}`,
      );
      if (d !== null) {
        return d;
      }
    }
  }
  const short = (v: unknown) => {
    const s = stableStringify(v) ?? 'undefined';
    return s.length > 120 ? s.slice(0, 120) + '…' : s;
  };
  return `${path}: editor ${short(a)} != shared ${short(b)}`;
}

/**
 * Make the set-valued StateConfigs known to `from` (registered by an
 * extension, or used there) known to `to` too, so that `to` joins the
 * per-member entries it reads into sets the way `from` does. A StateConfig
 * whose key contains the member separator is shared too: the reader keeps
 * an entry of that name as an ordinary key only when it knows a StateConfig
 * for it (see joinSetMembers).
 */
function shareSetStateConfigs(from: LexicalEditor, to: LexicalEditor): void {
  for (const [type, info] of from._nodes) {
    const target = to._nodes.get(type);
    if (target === undefined) {
      continue;
    }
    const {sharedConfigMap} = target.sharedNodeState;
    for (const stateConfig of info.sharedNodeState.sharedConfigMap.values()) {
      if (
        (isSetStateConfig(stateConfig) ||
          stateConfig.key.includes(SET_MEMBER_SEPARATOR)) &&
        !sharedConfigMap.has(stateConfig.key)
      ) {
        sharedConfigMap.set(stateConfig.key, stateConfig);
      }
    }
  }
}

/**
 * Development self-check of a whole container: a fresh reader (a new editor
 * with the same nodes) reads the container's shared content, and the result
 * must equal the editor's container (node types, fields, NodeState, list
 * structure, link fields, text and formats; derived fields aside). Catches
 * writer and reader mapping bugs alike.
 */
export function checkContainer(
  state: State,
  cs: CS,
  editorState: EditorState,
): string[] {
  if (state.hidden !== null || state.unknownTypes.size > 0) {
    return [];
  }
  const live = editorState.read(() => {
    const node = $getNodeByKey(cs.key);
    return $isElementNode(node) && node.isAttached()
      ? $deepJSON(node, $runNodes(state))
      : null;
  });
  if (live === null) {
    return [];
  }
  const derived = new Set<string>();
  for (const {klass} of state.editor._nodes.values()) {
    const spec = getContainerGroupSpec(klass);
    if (spec !== null) {
      spec.derived.forEach(f => derived.add(f));
    }
  }
  const fresh = createEditor({
    namespace: '@lexical/y self-check',
    nodes: [...state.editor._nodes.values()].map(info => info.klass),
    onError: e => {
      throw e;
    },
  });
  shareSetStateConfigs(state.editor, fresh);
  let read: Attrs | null = null;
  let problem: string | null = null;
  try {
    fresh.update(
      () => {
        const freshState = new State(fresh, state.doc, state.root);
        freshState.blockIds = state.blockIds;
        const reader = new Reader(freshState);
        let el: ElementNode;
        if (cs.y === state.root) {
          el = $getRoot();
        } else {
          el = $parseSerializedNode({
            ...live,
            $slots: undefined,
            children: [],
          } as unknown as SerializedLexicalNode) as ElementNode;
          $getRoot().append(el);
        }
        reader.$readFull(freshState.newCS(cs.y, el.getKey(), cs.kind), el);
        read = $deepJSON(el);
      },
      {discrete: true},
    );
  } catch (e) {
    problem = `container ${String(cs.key)} could not be read: ${String(e)}`;
  }
  if (problem !== null) {
    return [problem];
  }
  if (read === null) {
    return [];
  }
  const groupTypes = new Set<string>();
  for (const {klass} of state.editor._nodes.values()) {
    const spec = getContainerGroupSpec(klass);
    if (spec !== null) {
      groupTypes.add(spec.klass.getType());
    }
  }
  // A block id that blocks in other containers store too is settled across
  // the document (see Reader#$settleIds), which a read of this container
  // alone cannot do: there, the editor's id is taken.
  if (state.repeatedIds.size > 0) {
    forgiveRepeatedIds(live as Attrs, read as Attrs, state.repeatedIds);
  }
  const d = firstDifference(
    stripGroupText(stripDerived((live as Attrs).children, derived), groupTypes),
    stripGroupText(stripDerived((read as Attrs).children, derived), groupTypes),
    `container ${String(cs.key)}`,
  );
  return d === null ? [] : [d];
}

/**
 * Whether the text class of `attrs` keeps no format bits: its setFormat is
 * its own (a code highlight's ignores them), so a reader shows none.
 */
function dropsFormats(state: State, attrs: Attrs): boolean {
  const type = decodeFormatValue(attrs[TYPE_KEY] ?? null);
  const info = state.editor._nodes.get(
    typeof type === 'string' ? type : 'text',
  );
  return (
    info !== undefined &&
    info.klass.prototype instanceof TextNode &&
    (info.klass.prototype as TextNode).setFormat !==
      TextNode.prototype.setFormat
  );
}

/**
 * Where the editor and a read of one container give a block different ids,
 * one of which the document stores on several blocks, take the editor's.
 */
function forgiveRepeatedIds(
  live: Attrs,
  read: Attrs,
  repeated: ReadonlySet<string>,
): void {
  const idOf = (json: Attrs): unknown => {
    const st = json.$;
    return st !== null && typeof st === 'object' && !Array.isArray(st)
      ? (st as Attrs)[blockIdState.key]
      : undefined;
  };
  const id = idOf(read);
  const mine = idOf(live);
  if (
    id !== mine &&
    ((typeof id === 'string' && repeated.has(id)) ||
      (typeof mine === 'string' && repeated.has(mine)))
  ) {
    read.$ = {...(read.$ as Attrs), [blockIdState.key]: mine};
  }
  const a = live.children;
  const b = read.children;
  if (Array.isArray(a) && Array.isArray(b) && a.length === b.length) {
    for (let i = 0; i < a.length; i++) {
      const x = a[i];
      const y = b[i];
      if (
        x !== null &&
        typeof x === 'object' &&
        y !== null &&
        typeof y === 'object'
      ) {
        forgiveRepeatedIds(x as Attrs, y as Attrs, repeated);
      }
    }
  }
  const sa = live.$slots;
  const sb = read.$slots;
  if (
    sa !== null &&
    typeof sa === 'object' &&
    sb !== null &&
    typeof sb === 'object'
  ) {
    for (const name in sa as Attrs) {
      const x = (sa as Attrs)[name];
      const y = (sb as Attrs)[name];
      if (
        x !== null &&
        typeof x === 'object' &&
        y !== null &&
        typeof y === 'object'
      ) {
        forgiveRepeatedIds(x as Attrs, y as Attrs, repeated);
      }
    }
  }
}
