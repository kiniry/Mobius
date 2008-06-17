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
import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.swt.widgets.Shell;

import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeEditor;
import umbra.editor.DocumentSynchroniser;
import umbra.lib.GUIMessages;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraSynchronisationException;



/**
 * This class is responsible for action that is performed after
 * a double click event in a byte code editor window. This triggers a
 * synchronisation action which relates the position clicked within the
 * byte code editor to the source code in the corresponding Java file editor.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 * @see    BytecodeDocument
 */
public class BytecodeDoubleClickStrategy implements ITextDoubleClickStrategy {


  /**
   * This is an object which handles the calculations of the synchronisation
   * positions.
   */
  private DocumentSynchroniser my_synchroniser;

  /**
   * This method implements the reaction on the double click in
   * a byte code editor. It synchronises the position clicked within the
   * byte code editor to the source code in the corresponding Java file
   * editor. Most the information about the selected area is not used.
   * Only the position of the cursor is taken into account.
   *
   * @param a_selection the selected area of the byte code document
   */
  public final void doubleClicked(final ITextViewer a_selection) {
    final int pos = a_selection.getSelectedRange().x;

    if (pos < 0)
      return;

    final BytecodeDocument bDoc = (BytecodeDocument)a_selection.getDocument();
    final Shell sh = bDoc.getEditor().getSite().getShell();
    try {
      getDocSynch(bDoc).synchronizeBS(pos);
    } catch (UmbraLocationException e) {
      GUIMessages.messageWrongLocation(sh, GUIMessages.SYNCH_MESSAGE_TITLE, e);
    } catch (UmbraSynchronisationException e) {
      BytecodeSynchrAction.wrongSynchronisationMessage(sh,
        GUIMessages.SYNCH_MESSAGE_TITLE);
    }
  }

  /**
   * This method lazily provides the object which performs the synchronisation
   * operations.
   *
   * @param a_doc a byte code document for which the synchronisation is
   *   performed
   * @return a {@link DocumentSynchroniser} which performs the synchronisation
   *   operations
   */
  private DocumentSynchroniser getDocSynch(final BytecodeDocument a_doc) {
    if (my_synchroniser == null) {
      final BytecodeEditor editor = a_doc.getEditor();
      final CompilationUnitEditor jsceditor =
                              editor.getRelatedEditor();
      my_synchroniser = new DocumentSynchroniser(a_doc,
                              jsceditor.getDocumentProvider().
                              getDocument(jsceditor.getEditorInput()));
    }
    return my_synchroniser;
  }
}
