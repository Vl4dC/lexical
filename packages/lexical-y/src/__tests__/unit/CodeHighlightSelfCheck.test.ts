/**
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 */

// @vitest-environment node

// The development self-check compares a write with what a reader shows,
// under the same rules: a code highlight node stored without a segment key
// is read without one (the check gives it none), and a code highlight
// keeps no format bits, so a stored bold is not shown (the check ignores
// it). Before, both warned on keystrokes in code blocks (soak A2: `format
// k`, `format f:bold`).

import * as Y from '@y/y';
import {$getRoot, type ElementNode, type TextNode} from 'lexical';
import {expect, test} from 'vitest';

import {flush, freshReader, type Peer} from '../utils/harness';

/** A reader (self-check on) of a code block stored as `parts`. */
async function readCode(
  parts: [string, Record<string, unknown>][],
): Promise<Peer> {
  const doc = new Y.Doc({gc: false});
  doc.clientID = 5;
  const root = doc.get('lexical-y');
  doc.transact(() => {
    root.setAttr('lexical-y:1', true);
    root.setAttr('k:code', 'line');
    let at = 0;
    for (const [text, attrs] of parts) {
      root.insert(at, text, attrs);
      at += text.length;
    }
    const marker = new Y.Node('¶');
    root.insert(at, [marker]);
    marker.setAttr('t', 'code');
  });
  return freshReader({doc, nodes: undefined} as unknown as Peer);
}

async function typeAtEnd(p: Peer) {
  p.update(() => {
    const code = $getRoot().getFirstChild() as ElementNode;
    (code.getLastChild() as TextNode).select().insertText('x');
  });
  await flush();
}

test('a code highlight stored without a segment key: no self-check warning on a keystroke', async () => {
  const p = await readCode([
    ['zubimex zubimix ', {t: 'code-highlight'}],
    ['\n', {}],
    ['Beborex beborix', {t: 'code-highlight'}],
  ]);
  await typeAtEnd(p);
  expect(p.describe()).toContain('beborixx');
  expect(p.warnings.filter(w => w.includes('self-check'))).toEqual([]);
  // The typed character is stored as part of its node.
  expect((await freshReader(p)).describe()).toBe(p.describe());
});

test('a code highlight stored bold: no self-check warning on a keystroke', async () => {
  const p = await readCode([
    ['plain ', {k: 'a.1', t: 'code-highlight'}],
    ['bold', {'f:bold': true, k: 'a.2', t: 'code-highlight'}],
  ]);
  await typeAtEnd(p);
  expect(p.describe()).toContain('boldx');
  expect(p.warnings.filter(w => w.includes('self-check'))).toEqual([]);
});
