package ie.ucd.bon.plugin.ui.actions;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;

public abstract class SelectedProjectActionDelegate extends AbstractActionDelegate {

  public void run(IAction action) {
    ISelection selection = getSelection();
    if (selection instanceof IStructuredSelection) {
      Object firstEl = ((IStructuredSelection)selection).getFirstElement();
      if (firstEl instanceof IProject) {
        run(action, (IProject)firstEl);
      } else if (firstEl instanceof IJavaProject) {
        run(action, ((IJavaProject)firstEl).getProject());
      }
      
    }
  }

  protected abstract void run(IAction action, IProject project);
  
}
