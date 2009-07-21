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
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.lib.FileNames;
import umbra.lib.GUIMessages;

/**
 * The action is used to commit changes made to Java source code.
 * After running it the rebuild action will create a byte code related
 * to the commited version.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class CommitAction implements IEditorActionDelegate {

  /**
   * The editor for the corresponding Java file.
   */
  private CompilationUnitEditor my_editor;

  /**
   * The method saves the editor for the Java code file.
   *
   * @param an_action the GUI action which triggered the editor change
   * @param a_target_editor the editor of the Java source code file
   */
  public final void setActiveEditor(final IAction an_action,
                                    final IEditorPart a_target_editor) {
    my_editor = (CompilationUnitEditor)a_target_editor;
  }

  /**
   * This method is invoked when the Umbra "Commit" button is pressed
   * in a Java file editor. It saves the current Java file and deletes
   * from workspace the original class file which contains the result
   * of Java compilation (@see BytecodeEditor#doSave(IProgressMonitor)).
   *
   * @param an_action the action that triggered the operation
   * @see org.eclipse.ui.IActionDelegate#run(IAction)
   */
  public final void run(final IAction an_action) {
    my_editor.doSave(null);
    final IFile file = ((FileEditorInput)my_editor.getEditorInput()).getFile();
    IFile cfile = null;
    try {
      cfile = FileNames.getClassFileFile(file, my_editor);
    } catch (JavaModelException e1) {
      MessageDialog.openError(my_editor.getSite().getShell(),
                              GUIMessages.COMMIT_MESSAGE_TITLE,
                              GUIMessages.DISAS_CLASSFILEOUTPUT_PROBLEMS);
    }
    final IPath cpath = cfile.getFullPath();
    final String fnameFrom = FileNames.getSavedClassFileNameForClass(cpath);
    final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    final IFile fileFrom = root.getFile(new Path(fnameFrom));
    try {
      fileFrom.delete(true, null);
    } catch (CoreException e) {
      MessageDialog.openError(my_editor.getSite().getShell(),
                              GUIMessages.COMMIT_MESSAGE_TITLE,
                              GUIMessages.FAILED_CLASS_FILE_OPERATION);
    }
  }

  /**
   * The method reacts when the selected area changes in the Java
   * source code editor. Currently, it does nothing.
   *
   * @param an_action the action which triggered the selection change
   * @param a_selection the new selection
   */
  public void selectionChanged(final IAction an_action,
                               final ISelection a_selection) {
  }

}
