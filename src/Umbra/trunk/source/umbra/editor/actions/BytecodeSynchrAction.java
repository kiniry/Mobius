/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions;

import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.swt.widgets.Shell;

import sun.reflect.ReflectionFactory.GetReflectionFactoryAction;
import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditorContributor;
import umbra.editor.DocumentSynchroniser;
import umbra.lib.EclipseIdentifiers;
import umbra.lib.GUIMessages;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraSynchronisationException;

/**
 * This class defines action of the synchronisation for a byte code
 * position with an appropriate point in the source code.
 *
 * @see umbra.editor.BytecodeDocument
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeSynchrAction extends BytecodeEditorAction {

  /**
   * This is an object which handles the calculations of the synchronisation
   * positions.
   */
  private DocumentSynchroniser my_synchroniser;

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
    super(EclipseIdentifiers.SYNCHRONIZE_ACTION_NAME, a_contributor,
          a_bytecode_contribution);
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
    final Shell parent = getEditor().getSite().getShell();
    try {
      getDocSynch().synchronizeBS(off);
    } catch (UmbraLocationException e) {
      GUIMessages.messageWrongLocation(parent, getDescription(), e);
    } catch (UmbraSynchronisationException e) {
      wrongSynchronisationMessage(parent, getDescription());
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
    MessageDialog.openError(a_shell, a_title, GUIMessages.NOINSTRUCTION_MSG);
  }

  /**
   * This method lazily provides the object which performs the synchronisation
   * operations.
   *
   * @return a {@link DocumentSynchroniser} which performs the synchronisation
   *   operations
   */
  private DocumentSynchroniser getDocSynch() {
    if (getEditor().getRelatedEditor() == null)
      getEditor().findRelatedEditor();
    final CompilationUnitEditor jsceditor =
                            getEditor().getRelatedEditor();
    my_synchroniser = new DocumentSynchroniser(getEditor().getDocument(),
                            jsceditor.getDocumentProvider().
                            getDocument(jsceditor.getEditorInput()));
    return my_synchroniser;
  }

  /**
   * Highlights the area in the source code editor which corresponds to
   * the marked area in the byte code editor. Works correctly only inside a
   * method body.
   *
   * @param a_pos index of line in byte code editor. Lines in related source
   *   code editor corresponding to this line will be highlighted.
   * @throws UmbraLocationException in case a position is reached in the
   *   source code or byte code editor which does not exists there
   * @throws UmbraSynchronisationException in case there is no instruction
   *   line which can be reasonably associated with the given position
   */
  public void synchronizeBS(final int a_pos)
    throws UmbraLocationException, UmbraSynchronisationException {
    final DocumentSynchroniser synch = getDocSynch();
    synch.synchronizeBS(a_pos);
  }

}
