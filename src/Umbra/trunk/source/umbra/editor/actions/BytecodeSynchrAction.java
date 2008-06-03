/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.swt.widgets.Shell;

import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeEditorContributor;
import umbra.lib.GUIMessages;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraSynchronisationException;

/**
 * This class defines action of the synchronisation for a byte code
 * position with an appropriate point in the source code.
 *
 * @see BytecodeDocument
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeSynchrAction extends BytecodeEditorAction {

  /**
   * The constructor of the action. It only registers the name of the
   * action in the eclipse environment.
   *
   * @param a_contributor the manager that initialises all the actions within
   *   the byte code plugin
   * @param a_bytecode_contribution the GUI elements contributed to the eclipse
   *   GUI by the byte code editor. This reference should be the same as in the
   *   parameter <code>a_contributor</code>.
   */
  public BytecodeSynchrAction(final BytecodeEditorContributor a_contributor,
                     final BytecodeContribution a_bytecode_contribution) {
    super("Synchronize", a_contributor, a_bytecode_contribution);
  }


  /**
   * This method runs the synchronisation of the current byte code
   * with the source code. It retrieves the current selection, extracts the
   * offset of the beginning of the selection and shows the related Java source
   * code document that corresponds to the offset.
   */
  public final void run() {
    final ITextSelection selection = (ITextSelection)getEditor().
                    getSelectionProvider().getSelection();
    final int off = selection.getOffset();
    final BytecodeDocument bDoc = (BytecodeDocument)getEditor().
                    getDocumentProvider().
                    getDocument(getEditor().getEditorInput());
    final Shell parent = getEditor().getSite().getShell();
    try {
      bDoc.synchronizeBS(off);
    } catch (UmbraLocationException e) {
      wrongLocationMessage(parent, getActionDefinitionId(), e);
    } catch (UmbraSynchronisationException e) {
      wrongSynchronisationMessage(parent, getActionDefinitionId());
    }
  }


  /**
   * Displays the message that no source code instruction can be reasonably
   * associated with the given position.
   *
   * @param a_shell the shell which displays the message
   * @param a_title the title of the message window
   */
  public static void wrongSynchronisationMessage(final Shell a_shell,
                                                 final String a_title) {
    MessageDialog.openError(a_shell,
                            a_title, GUIMessages.NOINSTRUCTION_MSG);
  }
}
