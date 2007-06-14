/*
 * Created on 2005-09-06
 */
package umbra.editor.actions.info;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

/**
 * TODO
 *
 * @author Wojtek Wąs
 */
public class InstalInfoAction implements IEditorActionDelegate {

  /**
   * TODO
   */
  private IEditorPart editor;

  /**
   * TODO
   */
  public void setActiveEditor(IAction action, IEditorPart targetEditor) {
    editor = targetEditor;
  }

  /**
   * TODO
   */
  public void run(IAction action) {

    IWorkspace workspace = ResourcesPlugin.getWorkspace();
    IFile file = workspace.getRoot().getFile(new Path("\\Info\\info.txt"));
    FileEditorInput input = new FileEditorInput(file);
    try {
      editor.getEditorSite().getPage().openEditor(input, "org.eclipse.ui.DefaultTextEditor");
    } catch (PartInitException e) {
      e.printStackTrace();
    }
  }

  /**
   * TODO
   */
  public void selectionChanged(IAction action, ISelection selection) {
  }
}
