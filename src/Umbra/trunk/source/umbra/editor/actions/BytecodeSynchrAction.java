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
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;

import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeEditor;
import umbra.editor.UmbraLocationException;

/**
 * This class defines action of the synchronization for a byte code
 * position with an appropriate point in the source code.
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
   * This method runs the synchronisation of the current byte code
   * with the source code. It retrieves the current selection, extracts the
   * offset of the beginning of the selection and shows the related Java source
   * code document that corresponds to the offset.
   */
  public final void run() {
    final ITextSelection selection = (ITextSelection)my_editor.
                    getSelectionProvider().getSelection();
    final int off = selection.getOffset();
    final BytecodeDocument bDoc = (BytecodeDocument)my_editor.
                    getDocumentProvider().
                    getDocument(my_editor.getEditorInput());
    final Shell parent = my_editor.getSite().getShell();
    try {
      bDoc.synchronizeBS(off);
    } catch (UmbraLocationException e) {
      wrongLocationMessage(parent, getActionDefinitionId(), e);
    }
  }

  /**
   * Displays the message that a wrong location has been reached.
   *
   * @param a_shell the shell which displays the message
   * @param a_title the title of the message window
   * @param an_ex the exception with the information to display
   */
  public static void wrongLocationMessage(final Shell a_shell,
                                          final String a_title,
                                          final UmbraLocationException an_ex) {
    MessageDialog.openError(a_shell,
                            a_title,
                            "Wrong location " + an_ex.getWrongLocation() +
                            " in a " +
                            (an_ex.isByteCodeDocument() ? "byte code" :
                                                    "Java") +
                            "document");
  }
}
