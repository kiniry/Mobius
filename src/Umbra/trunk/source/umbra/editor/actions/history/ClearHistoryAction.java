/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions.history;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.editor.BytecodeEditor;

/**
 * The bytecode editor action that removes historical versions of code.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class ClearHistoryAction implements IEditorActionDelegate {

  /**
   * The editor of the bytecode for which we clear the history.
   */
  private IEditorPart my_editor;

  /**
   * The method sets the editor for which the history should be cleared.
   *
   * @param an_action ignored
   * @param a_target_editor the editor to clear history for.
   */
  public final void setActiveEditor(final IAction an_action,
                                    final IEditorPart a_target_editor) {
    my_editor = a_target_editor;
  }

  /**
   * This method clears the history for the currently active editor.
   * It resets the counter of the historical versions and then
   * deletes all the files in the workspace that represent the
   * historical versions of the current file.
   *
   * @param an_action the action to clear the history
   *
   */
  public final void run(final IAction an_action) {
    ((BytecodeEditor)my_editor).clearHistory();
    for (int i = 0; i <= UmbraHelper.MAX_HISTORY; i++) {
      final String ext = UmbraHelper.BYTECODE_HISTORY_EXTENSION + i;
      final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      final IFile inputFile = ((FileEditorInput)my_editor.getEditorInput()).
                                                          getFile();
      final IPath active = inputFile.getFullPath();
      final String fname = active.toOSString().replaceFirst(
                             UmbraHelper.BYTECODE_EXTENSION, ext);
      final IFile file = root.getFile(new Path(fname));
      try {
        file.delete(true, null);
      } catch (CoreException e) {
        e.printStackTrace();
      }
      final String lastSegment = active.lastSegment().replaceFirst(
                               UmbraHelper.BYTECODE_EXTENSION,
                               UmbraHelper.CLASS_EXTENSION);
      final String clname = active.removeLastSegments(1).append("_" + i +
                                          "_" + lastSegment).toOSString();
      final IFile classFile = root.getFile(new Path(clname));
      try {
        classFile.delete(true, null);
      } catch (CoreException e) {
        e.printStackTrace();
      }
    }

  }

  /**
   * The method reacts when the selected area changes in the bytecode
   * editor. Currently, it does nothing.
   *
   * @param an_action the action which triggered the selection change
   * @param a_selection the new selection.
   */
  public void selectionChanged(final IAction an_action,
                               final ISelection a_selection) {
  }
}
