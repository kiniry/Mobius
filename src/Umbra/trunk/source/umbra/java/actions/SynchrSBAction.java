/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.java.actions;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeEditor;
import umbra.editor.DocumentSynchroniser;
import umbra.lib.EclipseIdentifiers;
import umbra.lib.FileNames;
import umbra.lib.GUIMessages;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraSynchronisationException;

/**
 * This class defines an action of synchronization positions
 * form source code to bytecode. It is available with the standard
 * Java editor.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class SynchrSBAction implements IEditorActionDelegate {

  /**
   * The editor of the Java source code.
   */
  private CompilationUnitEditor my_editor;

  /**
   * This is an object which handles the calculations of the synchronisation
   * positions.
   */
  private DocumentSynchroniser my_synchroniser;

  /**
   * The method sets the internal Java source code editor attribute.
   *
   * @param an_action the action which triggered the change of the editor
   * @param a_java_editor the new Java source code editor to be associated with
   * the action
   */
  public final void setActiveEditor(final IAction an_action,
                                    final IEditorPart a_java_editor) {
    my_editor = (CompilationUnitEditor)a_java_editor;
  }

  /**
   * This method handles the action of the synchronisation between the
   * source code and the bytecode i.e. it takes the selection in
   * the source code and shows the corresponding selection in the
   * bytecode.
   *
   * @param an_action the action that triggered the operation
   */
  public final void run(final IAction an_action) {
    final ITextSelection selection = (ITextSelection) my_editor.
                    getSelectionProvider().getSelection();
    final int off = selection.getOffset();
    final IFile activef = ((FileEditorInput)my_editor.getEditorInput()).
                                                      getFile();
    final IPath active = activef.getFullPath();
    final int lind = active.toPortableString().
                            lastIndexOf(FileNames.JAVA_EXTENSION);
    if (lind == -1) {
      MessageDialog.openError(my_editor.getSite().getShell(),
                  "Bytecode", "This is not a \"" +
                  FileNames.JAVA_EXTENSION + "\" file");
      return;
    }

    final IFile file = FileNames.getBTCFileName(activef, my_editor);
    final FileEditorInput input = new FileEditorInput(file);
    try {
      final BytecodeEditor bcEditor = (BytecodeEditor)my_editor.getSite().
                           getPage().openEditor(input,
                            EclipseIdentifiers.BYTECODE_EDITOR_CLASS,
                            true);
      if (bcEditor.isSaveOnCloseNeeded()) {
        MessageDialog.openWarning(my_editor.getSite().getShell(),
                      "Bytecode",
                      "The Bytecode editor needs being " +
                      "refreshed!");
        return;
      }
      final BytecodeDocument bDoc = ((BytecodeDocument)bcEditor.
                        getDocumentProvider().
                        getDocument(input));
      synchronizeWithMessages(off, bDoc);
    } catch (PartInitException e) {
      e.printStackTrace(); //TODO stack print https://mobius.ucd.ie/ticket/591
    }
  }

  /**
   * This method performs the synchronisation of the byte code document for
   * the given position in the source code document. This method additionally
   * pops up all the necessary messages in case exceptions are raised.
   *
   * @param an_offset a position in the source code editor. Lines in related
   *   byte code editor containing the line with this postion will
   *   be highlighted
   * @param a_bcode_doc the byte code document to synchronise
   */
  private void synchronizeWithMessages(final int an_offset,
                                       final BytecodeDocument a_bcode_doc) {
    final Shell parent = my_editor.getSite().getShell();
    try {
      getDocSynch(a_bcode_doc).synchronizeSB(an_offset, my_editor);
    } catch (UmbraLocationException e) {
      MessageDialog.openError(parent,
                              GUIMessages.SYNCH_MESSAGE_TITLE,
                              GUIMessages.substitute2(
                                  GUIMessages.WRONG_LOCATION_MSG,
                                  "" + e.getWrongLocation(),
                                  (e.isByteCodeDocument() ? "byte code" :
                                                            "Java")));
    } catch (UmbraSynchronisationException e) {
      MessageDialog.openError(parent,
                              GUIMessages.SYNCH_MESSAGE_TITLE,
                              GUIMessages.WRONG_SYNCHRONISATION_MSG);
    } catch (JavaModelException e) {
      MessageDialog.openError(parent,
                              GUIMessages.SYNCH_MESSAGE_TITLE,
                              GUIMessages.WRONG_JAVAACCESS_MSG);
    }
  }

  /**
   * Currently, does nothing.
   *
   * @param an_action see
   *   {@link org.eclipse.ui.IActionDelegate#selectionChanged(IAction,
   *          ISelection)}
   * @param a_selection see
   *   {@link org.eclipse.ui.IActionDelegate#selectionChanged(IAction,
   *          ISelection)}
   */
  public void selectionChanged(final IAction an_action,
                               final ISelection a_selection) {
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
      final CompilationUnitEditor jsceditor = my_editor;
      my_synchroniser = new DocumentSynchroniser(a_doc,
                              jsceditor.getDocumentProvider().
                              getDocument(jsceditor.getEditorInput()));
    }
    return my_synchroniser;
  }
}
