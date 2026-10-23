/**
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 */
// @vitest-environment node

import {
  buildEditorFromExtensions,
  configExtension,
  getExtensionDependencyFromEditor,
} from '@lexical/extension';
import {
  $createListItemNode,
  $createListNode,
  $isListItemNode,
  $isListNode,
  CheckListExtension,
  ListExtension,
  type ListItemNode,
  type ListType,
} from '@lexical/list';
import {RichTextExtension} from '@lexical/rich-text';
import * as Y from '@y/y';
import {
  $addUpdateTag,
  $createParagraphNode,
  $createTextNode,
  $getRoot,
  $getSelection,
  $isRangeSelection,
  $isTextNode,
  $onUpdate,
  defineExtension,
  type LexicalEditor,
  type LexicalNode,
  OUTDENT_CONTENT_COMMAND,
  REDO_COMMAND,
  UNDO_COMMAND,
} from 'lexical';
import {describe, expect, test} from 'vitest';

import {YBinding, YCollabExtension} from '../..';

const EXTENSIONS = [RichTextExtension, ListExtension, CheckListExtension];

/** A document written by another client, as a stored state. */
function seed($build: () => void): Uint8Array {
  const editor = buildEditorFromExtensions(
    defineExtension({dependencies: EXTENSIONS, name: 'undo-selection-seed'}),
  );
  editor.update(
    () => {
      $getRoot().clear();
      $build();
    },
    {discrete: true},
  );
  const doc = new Y.Doc();
  doc.clientID = 7;
  const binding = new YBinding(editor, doc, {captureTimeout: null});
  binding.start();
  binding.initialize();
  binding.dispose();
  return Y.encodeStateAsUpdate(doc);
}

/** An editor with YCollabExtension (and its UNDO_COMMAND handler). */
function open(
  state: Uint8Array,
  clientID: number,
): {editor: LexicalEditor; binding: YBinding; doc: Y.Doc} {
  const doc = new Y.Doc();
  doc.clientID = clientID;
  Y.applyUpdate(doc, state, 'load');
  const editor = buildEditorFromExtensions(
    defineExtension({
      dependencies: [
        ...EXTENSIONS,
        configExtension(YCollabExtension, {captureTimeout: 0, doc}),
      ],
      name: 'undo-selection',
      onError: e => {
        throw e;
      },
    }),
  );
  const {binding} = getExtensionDependencyFromEditor(
    editor,
    YCollabExtension,
  ).output;
  binding.initialize();
  return {binding, doc, editor};
}

const selection = (editor: LexicalEditor) =>
  editor.read(() => {
    const s = $getSelection();
    return $isRangeSelection(s)
      ? `${s.anchor.offset}-${s.focus.offset}`
      : String(s);
  });

const text = (editor: LexicalEditor) =>
  editor.read(() => $getRoot().getTextContent());

function $firstText() {
  const node = $getRoot().getFirstDescendant();
  if (!$isTextNode(node)) {
    throw new Error('no text');
  }
  return node;
}

describe('undo puts the selection back where the step started', () => {
  const state = seed(() =>
    $getRoot().append(
      $createParagraphNode().append($createTextNode('abc def')),
    ),
  );
  for (const how of ['binding.undo()', 'UNDO_COMMAND']) {
    const undo = (c: ReturnType<typeof open>) =>
      how === 'UNDO_COMMAND'
        ? c.editor.dispatchCommand(UNDO_COMMAND, undefined)
        : c.binding.undo();
    const redo = (c: ReturnType<typeof open>) =>
      how === 'UNDO_COMMAND'
        ? c.editor.dispatchCommand(REDO_COMMAND, undefined)
        : c.binding.redo();

    test(`a Backspace (${how})`, () => {
      const c = open(state, 1);
      c.editor.update(() => $firstText().select(4, 4), {discrete: true});
      c.editor.update(() => $firstText().spliceText(3, 1, '', true), {
        discrete: true,
      });
      expect([text(c.editor), selection(c.editor)]).toEqual(['abcdef', '3-3']);
      undo(c);
      expect([text(c.editor), selection(c.editor)]).toEqual(['abc def', '4-4']);
      // Redo puts back the selection from when the step was undone (mapped
      // through the redo), not the one it finds.
      c.editor.update(() => $firstText().select(7, 7), {discrete: true});
      redo(c);
      expect([text(c.editor), selection(c.editor)]).toEqual(['abcdef', '3-3']);
    });

    test(`typing over a selection (${how})`, () => {
      const c = open(state, 1);
      c.editor.update(() => $firstText().select(4, 7), {discrete: true});
      c.editor.update(
        () => {
          const s = $getSelection();
          if ($isRangeSelection(s)) {
            s.insertText('x');
          }
        },
        {discrete: true},
      );
      expect(text(c.editor)).toBe('abc x');
      undo(c);
      expect([text(c.editor), selection(c.editor)]).toEqual(['abc def', '4-7']);
    });
  }
});

const $li = (content: string) =>
  $createListItemNode().append($createTextNode(content));
const $wrap = (type: ListType, ...items: ListItemNode[]) =>
  $createListItemNode().append($createListNode(type).append(...items));

/** Every list item's own text and number, in document order. */
function numbers(editor: LexicalEditor): string[] {
  return editor.read(() => {
    const out: string[] = [];
    const walk = (node: LexicalNode) => {
      if ($isListItemNode(node)) {
        const own = node
          .getChildren()
          .filter(c => !$isListNode(c))
          .map(c => c.getTextContent())
          .join('');
        out.push(`${own || '(wrapper)'}:${node.getValue()}`);
      }
      if ('getChildren' in node) {
        for (const c of (
          node as unknown as {getChildren(): LexicalNode[]}
        ).getChildren()) {
          walk(c);
        }
      }
    };
    walk($getRoot());
    return out;
  });
}

describe('an undo started while the editor is updating', () => {
  const state = seed(() =>
    $getRoot().append(
      $createListNode('bullet').append(
        $li('First bullet'),
        $wrap('bullet', $li('Nested'), $wrap('bullet', $li('Deeper'))),
        $li('Second bullet'),
      ),
      $createListNode('number').append(
        $li('Ship'),
        $wrap('number', $li('Rich docs'), $li('Rich sheets')),
        $li('Measure'),
      ),
      $createListNode('check').append(
        $li('Storage'),
        $li('Co-editing'),
        $wrap('check', $li('Nested task')),
      ),
      $createParagraphNode().append($createTextNode('end')),
    ),
  );
  test.each([
    'binding.undo()',
    'UNDO_COMMAND',
    'inside an update',
    "in an update's $onUpdate",
  ])('is read in an update of its own: list numbers come back (%s)', how => {
    const c = open(state, 1);
    const before = numbers(c.editor);
    c.editor.update(
      () => {
        $getRoot()
          .getAllTextNodes()
          .find(n => n.getTextContent() === 'Nested task')!
          .select(5, 0);
      },
      {discrete: true},
    );
    c.editor.dispatchCommand(OUTDENT_CONTENT_COMMAND, undefined);
    expect(numbers(c.editor)).not.toEqual(before);
    if (how === 'binding.undo()') {
      c.binding.undo();
    } else if (how === 'UNDO_COMMAND') {
      c.editor.dispatchCommand(UNDO_COMMAND, undefined);
    } else if (how === 'inside an update') {
      c.editor.update(
        () => {
          $addUpdateTag('test');
          c.binding.undo();
        },
        {discrete: true},
      );
    } else {
      c.editor.update(() => $onUpdate(() => void c.binding.undo()), {
        discrete: true,
      });
    }
    expect(numbers(c.editor)).toEqual(before);
    // And the editor shows the document.
    const fresh = open(Y.encodeStateAsUpdate(c.doc), 2);
    expect(fresh.editor.getEditorState().toJSON()).toEqual(
      c.editor.getEditorState().toJSON(),
    );
  });
});
