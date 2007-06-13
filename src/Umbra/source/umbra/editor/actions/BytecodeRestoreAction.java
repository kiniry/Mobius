package umbra.editor.actions;

import java.io.IOException;

import javax.swing.JOptionPane;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;

/**
 * This class defines action of restoring bytecode from
 * history. Current verion is replaced with one of these
 * kept in history as a file with bt1, bt2, etc. extension
 *
 * @author BYTECODE Team (contact alx@mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeRestoreAction extends Action {

  /**
   * The current bytecode editor for which the action takes place.
   */
  private IEditorPart editor;

  /**
   * The manager that initialises all the actions within the
   * bytecode plugin.
   */
  private BytecodeEditorContributor contributor;

  /**
   * TODO should be the same as in contributor
   */
  private BytecodeContribution bytecodeContribution;

  /**
   * TODO
   *
   * @param contributor
   * @param bytecodeContribution
   */
  public BytecodeRestoreAction(BytecodeEditorContributor contributor,
                 BytecodeContribution bytecodeContribution) {
    super("Restore");
    this.contributor = contributor;
    this.bytecodeContribution = bytecodeContribution;
  }

  /**
   * An input dialog to insert number of version is shown.
   * Then the binary source file is replaced with the
   * appropriate historical version and new input is
   * generated and put into the editor window.
   */
  public void run() {
    String strnum = JOptionPane.showInputDialog("Input version number (0 to 2):", "0");
    int num = 0;
    if (strnum == "1") num = 1;
    else if (strnum == "2") num = 2;
    String ext = UmbraHelper.BYTECODE_HISTORY_EXTENSION + num;
    IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    IFile file = ((FileEditorInput)editor.getEditorInput()).getFile();
    IPath active = file.getFullPath();
    String fnameFrom = active.toOSString().replaceFirst(
                   UmbraHelper.BYTECODE_EXTENSION,
                   ext);
    IFile fileFrom = root.getFile(new Path(fnameFrom));
    if (!fileFrom.exists()) {
      Shell shell = editor.getSite().getShell();
      MessageDialog.openInformation(shell, "Restore bytecode",
          "The file " + fnameFrom + " does not exist");
      return;
    }
    try {
      file.delete(true, null);
      fileFrom.copy(active, true, null);
    } catch (CoreException e) {
      e.printStackTrace();
    }
    String lastSegment = active.lastSegment().replaceFirst(
                    UmbraHelper.BYTECODE_EXTENSION,
                    UmbraHelper.CLASS_EXTENSION);
    String clnameTo = active.removeLastSegments(1).append(lastSegment).toOSString();
    String clnameFrom = active.removeLastSegments(1).append("_" + num + "_" + lastSegment).toOSString();
    IFile classFrom = root.getFile(new Path(clnameFrom));
    IPath clpathTo = new Path(clnameTo);
    IFile classTo = root.getFile(clpathTo);
    try {
      classTo.delete(true, null);
      classFrom.copy(clpathTo, true, null);
    } catch (CoreException e) {
      e.printStackTrace();
    }
    try {
      ((BytecodeEditor)editor).refreshBytecode(active, null, null);
      IEditorInput input = new FileEditorInput(file);
      boolean[] modified = bytecodeContribution.getModified();
      bytecodeContribution.setModTable(modified);
      contributor.refreshEditor(editor, input);
    } catch (ClassNotFoundException e1) {
      e1.printStackTrace();
    } catch (CoreException e1) {
      e1.printStackTrace();
    } catch (IOException e1) {
      e1.printStackTrace();
    }
    contributor.synchrEnable();
  }

  /**
   * This method sets the bytecode editor for which the
   * restore action will be executed.
   *
   * @param part the bytecode editor for which the action will be executed
   */
  public void setActiveEditor(IEditorPart part) {
    editor = part;
  }
}
