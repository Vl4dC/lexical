/**
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 */

// @vitest-environment node

// A quote that holds paragraphs (a shadow root, as Meta Artifacts' quote is)
// holds only blocks. One client turns a paragraph into such a quote (the
// paragraph moves into it) while another types into the paragraph: the typed
// text lands next to the moved paragraph (a move, see Limits), and every
// client and fresh reader show it in a paragraph of its own, never as text
// directly inside the quote (which apps reading the tree throw on).

import {$createQuoteNode, $isQuoteNode} from '@lexical/rich-text';
import {
  $createParagraphNode,
  $getRoot,
  $isElementNode,
  type ElementNode,
} from 'lexical';
import {describe, expect, test} from 'vitest';

import {
  $block,
  $p,
  $selectIn,
  expectConverged,
  freshReader,
  type Peer,
  setup,
} from '../utils/harness';

function $moveIntoQuote(path: number[]) {
  // What a container quote's `> ` shortcut does: the paragraph moves into a
  // new quote in its place.
  const p = $block(path);
  const quote = $createQuoteNode({shadowRoot: true});
  p.insertBefore(quote);
  quote.append(p);
  p.selectEnd();
}

function $replaceWithQuote(path: number[]) {
  // The other way to write it: a new quote with a new paragraph holding the
  // old paragraph's children.
  const p = $block(path);
  const quote = $createQuoteNode({shadowRoot: true});
  const inner = $createParagraphNode();
  for (const child of p.getChildren()) {
    inner.append(child);
  }
  quote.append(inner);
  p.replace(quote);
  inner.selectEnd();
}

/** What each quote holds: block types, and anything else as `!type`. */
function quoteChildren(peer: Peer): string[][] {
  return peer.read(() =>
    $getRoot()
      .getChildren()
      .filter($isQuoteNode)
      .map(q =>
        (q as ElementNode)
          .getChildren()
          .map(c =>
            $isElementNode(c) && !c.isInline()
              ? c.getType()
              : `!${c.getType()}`,
          ),
      ),
  );
}

describe('a quote that holds paragraphs ‖ typing in the paragraph it takes', () => {
  for (const ids of [
    [1, 2],
    [2, 1],
  ]) {
    for (const [name, $wrap] of [
      ['moved into the quote', $moveIntoQuote],
      ['replaced by the quote', $replaceWithQuote],
    ] as const) {
      test(`ids ${ids}, ${name}`, async () => {
        const t = await setup(
          () => $getRoot().append($p('one'), $p('Lorem ipsum'), $p('end')),
          {ids},
        );
        t.offline();
        t.a.update(() => $wrap([1]));
        t.b.update(() => {
          $selectIn([1], 5).insertText('qa');
        });
        await t.sync();
        const fresh = await freshReader(t.a);
        for (const peer of [t.a, t.b, fresh]) {
          expect(quoteChildren(peer)).toEqual([['paragraph', 'paragraph']]);
        }
        await expectConverged(t.peers);
        // A later edit in the paragraph the read made stores it.
        t.b.update(() => {
          $selectIn([1, 0], 2).insertText('!');
        });
        await t.sync();
        await expectConverged(t.peers);
        expect(t.a.read(() => $getRoot().getTextContent())).toContain('qa!');
        for (const peer of [t.a, t.b]) {
          expect(quoteChildren(peer)).toEqual([['paragraph', 'paragraph']]);
        }
      });
    }
  }
});
