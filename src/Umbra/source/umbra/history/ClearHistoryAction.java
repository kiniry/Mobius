/*
 * Created on 2005-09-06
 *
 */
package umbra.history;

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
 * The action that removes historical versions of code.
 *
 * @author Wojtek W±s
 */
public class ClearHistoryAction implements IEditorActionDelegate {

  /**
   * The editor of the bytecode for which we clear the history.
   */
  private IEditorPart editor;

  /**
   * The method sets the editor for which the history should be cleared.
   *
   * @param action ignored
   * @param targetEditor the editor to clear history for.
   */
  public void setActiveEditor(IAction action, IEditorPart targetEditor) {
    editor = targetEditor;
  }

  /**
   * This method clears the history for the currently active editor.
   * It resets the counter of the historical versions and then
   * deletes all the files in the workspace that represent the
   * historical versions of the current file.
   *
   * @param action the action to clear the history
   *
   */
  public void run(IAction action) {
    ((BytecodeEditor)editor).clearHistory();
    for (int i = 0; i <= IHistory.maxHistory; i++) {
      String ext = UmbraHelper.BYTECODE_HISTORY_EXTENSION + i;
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFile inputFile = ((FileEditorInput)editor.getEditorInput()).getFile();
      IPath active = inputFile.getFullPath();
      String fname = active.toOSString().replaceFirst(
                             UmbraHelper.BYTECODE_EXTENSION, ext);
      IFile file = root.getFile(new Path(fname));
      try {
        file.delete(true, null);
      } catch (CoreException e) {
        e.printStackTrace();
      }
      String lastSegment = active.lastSegment().replaceFirst(
                               UmbraHelper.BYTECODE_EXTENSION,
                               UmbraHelper.CLASS_EXTENSION);
      String clname = active.removeLastSegments(1).append("_" + i +
                                          "_" + lastSegment).toOSString();
      IFile classFile = root.getFile(new Path(clname));
      try {
        classFile.delete(true, null);
      } catch (CoreException e) {
        e.printStackTrace();
      }
    }

  }

  /**
   * Currently does nothing.
   */
  public void selectionChanged(IAction action, ISelection selection) {
  }
}
