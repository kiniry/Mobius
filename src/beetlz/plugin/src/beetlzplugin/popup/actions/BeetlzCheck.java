package beetlzplugin.popup.actions;

import java.util.Iterator;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import beetlzplugin.runner.BeetlzRunner;

/**
 * Class for consistency checking menu item.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @beta-1
 */
public class BeetlzCheck implements IObjectActionDelegate {

  /** Selected resources. */
  private ISelection my_selection;

  /**
   * Constructor for Action1.
   */
  public BeetlzCheck() {
    super();
  }

  /**
   * @see IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
   */
  public void setActivePart(final IAction action, final IWorkbenchPart targetPart) {
    //my_shell = targetPart.getSite().getShell();
  }

  /**
   * @see IActionDelegate#selectionChanged(IAction, ISelection)
   */
  public void selectionChanged(final IAction action, final ISelection selection) {
    my_selection = selection;
  }  

  /**
   * Get the selected project instance from the current selection.
   */
  private IProject getSelectedProject() {
    return getSelectedProject(my_selection);
  }
  
  /**
   * Get the selected project instance from the provided selection.
   */
  public static IProject getSelectedProject(final ISelection selection) {
    if (!selection.isEmpty() && selection instanceof IStructuredSelection) {
      final IStructuredSelection sSelection = (IStructuredSelection)selection;
      for (final Iterator <?> iter = sSelection.iterator(); iter.hasNext();) {
        final Object element = iter.next();
        if (element instanceof IResource) {
          final IResource resource = (IResource) element;
          return resource.getProject();
        }
      }
    }
    return null;
  }

  @Override
  public void run(IAction action) {
    IProject project = getSelectedProject();
    if (project != null) {
      BeetlzRunner runner = new BeetlzRunner();
      runner.runChecker(getSelectedProject());
    } else {
      //TODO report error? Shouldn't really happen
    }
  }

}
