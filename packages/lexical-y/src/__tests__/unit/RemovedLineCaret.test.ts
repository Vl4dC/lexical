/**
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 */

// The caret is in a line a peer removes, and a block node (a table) follows
// it: the remote read puts the caret at the end of the line before (else
// the start of the line after), never at a point in the table, where the
// next Backspace would delete what a cell holds (R6-A seed 124).
// @vitest-environment node

import {$createListItemNode, $createListNode} from '@lexical/list';
import {$createTableNodeWithDimensions} from '@lexical/table';
import {
  $createTextNode,
  $getRoot,
  $getSelection,
  $isRangeSelection,
  $isTextNode,
  type ElementNode,
  type LexicalNode,
} from 'lexical';
import {expect, test} from 'vitest';

import {
  $p,
  $selectIn,
  describeNode,
  flush,
  type Peer,
  setup,
} from '../utils/harness';

const caret = (p: Peer) =>
  p.read(() => {
    const s = $getSelection();
    if (!$isRangeSelection(s)) {
      return String(s);
    }
    const n: LexicalNode = s.anchor.getNode();
    return `${s.anchor.type} ${
      $isTextNode(n)
        ? JSON.stringify(n.getTextContent())
        : describeNode(n).slice(0, 60)
    }@${s.anchor.offset}`;
  });

function $table(): ElementNode {
  const table = $createTableNodeWithDimensions(1, 1, false);
  const cell = (
    table.getFirstChild() as ElementNode
  ).getFirstChild() as ElementNode;
  (cell.getFirstChild() as ElementNode).append($createTextNode('x'));
  cell.append(
    $createListNode('bullet').append(
      $createListItemNode().append($createTextNode('alpha beta gamma')),
    ),
  );
  return table;
}

for (const shape of ['empty', 'with text'] as const) {
  for (const before of [true, false]) {
    test(`a ${shape} line before a table, removed by a peer while the caret is in it (${
      before ? 'a line before it' : 'first in the document'
    }): the caret stays out of the table`, async () => {
      const {a, b, sync} = await setup(() => {
        $getRoot().append(
          ...(before ? [$p('top')] : []),
          shape === 'empty' ? $p('') : $p('gone'),
          $table(),
          $p('end'),
        );
      });
      const at = before ? 1 : 0;
      b.update(() => {
        if (shape === 'empty') {
          ($getRoot().getChildAtIndex(at) as ElementNode).select(0, 0);
        } else {
          $selectIn([at], 2);
        }
      });
      a.update(() => {
        $getRoot().getChildAtIndex(at)!.remove();
      });
      await sync();
      await flush();
      const after = caret(b);
      // The end of "top", or the start of "end".
      expect(
        before
          ? ['text "top"@3', 'element paragraph("top")@1']
          : ['text "end"@0', 'element paragraph("end")@0'],
      ).toContain(after);
      const text = a.read(() => $getRoot().getTextContent());
      expect(text).toContain('alpha beta gamma');
    });
  }
}
