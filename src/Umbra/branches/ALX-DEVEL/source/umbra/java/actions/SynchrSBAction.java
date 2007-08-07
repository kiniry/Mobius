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
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeEditor;

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
   * This method handles the action of the syncronisation between the
   * source code and the bytecode i.e. it takes the selection in
   * the source code and shows the corresponding selection in the
   * bytecode.
   *
   * @param an_action the action that triggered the operation
   */
  public final void run(final IAction an_action) {
    final ITextSelection selection = (ITextSelection)my_editor.
                    getSelectionProvider().getSelection();
    final int off = selection.getOffset();
    final IFile activef = ((FileEditorInput)my_editor.getEditorInput()).
                                                      getFile();
    final IPath active = activef.getFullPath();
    final int lind = active.toPortableString().
                            lastIndexOf(UmbraHelper.JAVA_EXTENSION);
    if (lind == -1) {
      MessageDialog.openError(my_editor.getSite().getShell(),
                  "Bytecode", "This is not a \"" +
                  UmbraHelper.JAVA_EXTENSION + "\" file");
      return;
    }
    final IFile file = UmbraHelper.getBTCFileName(activef, my_editor);
    final FileEditorInput input = new FileEditorInput(file);
    try {
      final BytecodeEditor bcEditor = (BytecodeEditor)my_editor.getSite().
                           getPage().openEditor(input,
                            "umbra.BytecodeEditor",
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
      bDoc.synchronizeSB(off, bcEditor);
    } catch (PartInitException e) {
      e.printStackTrace();
    }
  }

  /**
   * Currently, does nothing.
   *
   * @param an_action see {@ref IActionDelegate#selectionChanged(IAction,
   *                       ISelection)}
   * @param a_selection see {@ref IActionDelegate#selectionChanged(IAction,
   *                       ISelection)}
   */
  public void selectionChanged(final IAction an_action,
                               final ISelection a_selection) {
  }

}
