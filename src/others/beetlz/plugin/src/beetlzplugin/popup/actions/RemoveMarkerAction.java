package beetlzplugin.popup.actions;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import beetlzplugin.runner.BeetlzRunner;

/**
 * Action for remove markers menu item.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class RemoveMarkerAction implements IObjectActionDelegate {
  /** Selected resources. */
  private ISelection my_selection;

  /**
   * Constructor for Action1.
   */
  public RemoveMarkerAction() {
    super();
  }

  /**
   * @see IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
   */
  public void setActivePart(final IAction action, final IWorkbenchPart targetPart) {
  }
  
  /**
   * @see IActionDelegate#selectionChanged(IAction, ISelection)
   */
  public void selectionChanged(final IAction action, final ISelection selection) {
    my_selection = selection;
  }

  /**
   * Run this action. Remove all Beetlz markers for the selected project.
   * @see IActionDelegate#run(IAction)
   */
  public void run(final IAction action) {

    IProject project = BeetlzCheck.getSelectedProject(my_selection);
    if (project != null) {
      try {
        BeetlzRunner.removeAllBeetlzMarkers(project);
      } catch (CoreException e) { }
    }
    
  }

}
