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
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.editor.BytecodeEditor;

/**
 * This class defines an action that adds current bytecode snapshot
 * to the history stack. The stack is implemented in the file system.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class HistoryAction implements IEditorActionDelegate {

  /**
   * The editor for which a historical snapshot should be added.
   */
  private IEditorPart my_editor;

  /**
   * The method sets the .btc file editor for which the history item
   * should be added.
   *
   * @param an_action currently ignored
   * @param a_target_editor the editor to clear the history for
   */
  public final void setActiveEditor(final IAction an_action,
                                    final IEditorPart a_target_editor) {
    my_editor = a_target_editor;
  }

  /**
   * This method increments the counter of the existing history snapshots.
   * In case the history stack is full an appropriate message is
   * displayed. Otherwise, the files for the currently edited bytecode
   * file (i.e. .btc file and .class file) are saved into the history.
   *
   * @param an_action the action to add the history snapshot
   */
  public final void run(final IAction an_action) {
    final int num = ((BytecodeEditor)my_editor).newHistory();
    if (num == -1) {
      MessageDialog.openInformation(my_editor.getEditorSite().getShell(),
                                   "History", "History is already full.");
      return;
    }
    final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();

    final IFile fileFrom = ((FileEditorInput)my_editor.getEditorInput()).
                                                       getFile();
    saveBTCHistoryFile(fileFrom, num, root);
    saveClassHistoryFile(fileFrom, num, root);
  }

  /**
   * This method saves under the history slot number in <code>a_hist_num</code>
   * the bytecode classfile that corresponds to the file in
   * <code>a_file_from</code>. The operation is done relatively to the
   * workpsace specified in <code>the_root</code>.
   *
   * @param a_file_from a Java file for which the classfile is to be inserted
   *                    into the history
   * @param a_hist_num a history slot number under which the file should
   *                   be saved
   * @param the_root the workspace root for all the operations
   */
  private static void saveClassHistoryFile(final IFile a_file_from,
                                    final int a_hist_num,
                                    final IWorkspaceRoot the_root) {
    final IPath active = a_file_from.getFullPath();
    final String lastSegment = UmbraHelper.replaceLast(active.lastSegment(),
                                    UmbraHelper.BYTECODE_EXTENSION,
                                    UmbraHelper.CLASS_EXTENSION);
    final String clnameFrom = active.removeLastSegments(1).append(lastSegment).
                                                     toOSString();
    final String clnameTo = active.removeLastSegments(1).append("_" +
                                           a_hist_num + "_" +
                                           lastSegment).toPortableString();
    final IFile classFrom = the_root.getFile(new Path(clnameFrom));
    final IPath clpathTo = new Path(clnameTo);
    final IFile classTo = the_root.getFile(clpathTo);
    try {
      classTo.delete(true, null);
      classFrom.copy(clpathTo, true, null);
    } catch (CoreException e) {
      e.printStackTrace();
    }
  }

  /**
   * This method saves under the history slot number in <code>a_hist_num</code>
   * the bytecode classfile that corresponds to the file in
   * <code>a_file_from</code>. The operation is done relatively to the
   * workpsace specified in <code>the_root</code>.
   *
   * @param a_file_from a Java file for which the classfile is to be inserted
   *                    into the history
   * @param a_hist_num a history slot number under which the file should
   *                   be saved
   * @param the_root the workspace root for all the operations
   */
  private static void saveBTCHistoryFile(final IFile a_file_from,
                                   final int a_hist_num,
                                   final IWorkspaceRoot the_root) {
    final IPath active = a_file_from.getFullPath();
    final String ext = UmbraHelper.BYTECODE_HISTORY_EXTENSION + a_hist_num;
    final String fnameTo = UmbraHelper.replaceLast(active.toOSString(),
              UmbraHelper.BYTECODE_EXTENSION, ext);
    final IPath pathTo = new Path(fnameTo);
    final IFile fileTo = the_root.getFile(pathTo);
    try {
      fileTo.delete(true, null);
      a_file_from.copy(pathTo, true, null);
    } catch (CoreException e) {
      e.printStackTrace();
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
