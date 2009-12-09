package ie.ucd.bon.plugin.ui.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;

public abstract class AllSelectionsActionDelegate extends AbstractActionDelegate {

  public void run(IAction action) {
    ISelection selection = getSelection();
    if (selection instanceof IStructuredSelection) {
      run(action, ((IStructuredSelection)selection).toArray());
    }
  }
  
  protected abstract void run(IAction action, Object[] selectedElements); 

}
