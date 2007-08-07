/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.ui.IEditorPart;
import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeEditor;

/**
 * This class defines action of synchronization bytecode
 * position with appropriate point in source code.
 *
 * @see BytecodeDocument
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeSynchrAction extends Action {

  /**
   * The current bytecode editor for which the action takes place.
   */
  private BytecodeEditor my_editor;

  /**
   * The constructor of the action. It only registers the name of the
   * action in the eclipse environment.
   */
  public BytecodeSynchrAction() {
    super("Synchronize");
  }

  /**
   * This method sets the bytecode editor for which the
   * synchronization action will be executed.
   *
   * @param a_target_editor the bytecode editor for which the action will be
   *        executed
   */
  public final void setActiveEditor(final IEditorPart a_target_editor) {
    my_editor = (BytecodeEditor)a_target_editor;
  }

  /**
   * This method consults the current selection, extracts the
   * offset of the selection and shows the related Java source
   * code document with the ???
   * TODO
   */
  public final void run() {
    final ITextSelection selection = (ITextSelection)my_editor.
                    getSelectionProvider().getSelection();
    final int off = selection.getOffset();
    final BytecodeDocument bDoc = (BytecodeDocument)my_editor.
                    getDocumentProvider().
                    getDocument(my_editor.getEditorInput());
    bDoc.synchronizeBS(off);
  }
}
