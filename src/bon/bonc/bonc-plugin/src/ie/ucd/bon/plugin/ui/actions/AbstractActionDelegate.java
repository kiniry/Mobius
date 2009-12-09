package ie.ucd.bon.plugin.ui.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

public abstract class AbstractActionDelegate implements IObjectActionDelegate {

  private IWorkbenchPart targetPart;
  private ISelection selection;

  public void setActivePart(IAction action, IWorkbenchPart targetPart) {
    this.targetPart = targetPart;
  }

  public void selectionChanged(IAction action, ISelection selection) {
    this.selection = selection;
  }

  public IWorkbenchPart getTargetPart() {
    return targetPart;
  }

  public ISelection getSelection() {
    return selection;
  }
  
}
