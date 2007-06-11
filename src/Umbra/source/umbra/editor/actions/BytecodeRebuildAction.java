package umbra.editor.actions;

import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.Action;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;

/**
 * This class defines action of restoring the previous version
 * of binary file (remembered with the name exteneded with '_')
 * and then generating bytecode directly from it.
 * All changes made to bytecode are cancelled then.
 * This action is equall to saving Java source file (such that
 * binary file are restored) and generating bytecode from this.
 */
public class BytecodeRebuildAction extends Action {

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
   * This method sets the bytecode editor for which the
   * rebuild action will be executed.
   *
   * @param targetEditor the bytecode editor for which the action will be
   *    executed
   */
  public void setActiveEditor(final IEditorPart targetEditor) {
    editor = targetEditor;
  }

  /**
   * TODO
   *
   * @param contributor the
   */
  public BytecodeRebuildAction(
      final BytecodeEditorContributor contributor) {
    super("Rebuild");
    this.contributor = contributor;
  }

  /**
   * '_' file is chosen and rewritten into ordinary binary
   * file. The modificated binaries are removed, input is
   * updated and the editor window appropriately restored.
   *
   */
  public void run() {
    IFile file = ((FileEditorInput)editor.getEditorInput()).getFile();
    IPath active = file.getFullPath();
    String fnameTo = active.toOSString().replaceFirst(
                  UmbraHelper.BYTECODE_EXTENSION,
                  UmbraHelper.CLASS_EXTENSION);
    String lastSegment = active.lastSegment().replaceFirst(
                  UmbraHelper.BYTECODE_EXTENSION,
                  UmbraHelper.CLASS_EXTENSION);
    String fnameFrom = active.removeLastSegments(1).append("_" + lastSegment).toOSString();
    IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    IFile fileFrom = root.getFile(new Path(fnameFrom));
    IPath pathTo = new Path(fnameTo);
    IFile fileTo = root.getFile(pathTo);
    if (fileFrom.exists()) {
      try {
        fileTo.delete(true, null);
        fileFrom.copy(pathTo, true, null);
      } catch (CoreException e) {
        e.printStackTrace();
      }
    }
    try {
      ((BytecodeEditor)editor).refreshBytecode(active, null, null);
      IEditorInput input = new FileEditorInput(file);
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
}
