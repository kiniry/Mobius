package escjava.plugin.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;

import escjava.plugin.WarningDeclarationsAction;

/**
 * This class implements the action that opens and
 * positions an editor on an associated declaration of
 * a marker.
 * 
 * @author David R. Cok
 */
public class GoToDecl extends AEscjavaAction {
  private ISelection selection;

  /** {@inheritDoc} */
  public final void run(final IAction action) {
    //System.err.println("ACTION " + action.getClass());
    WarningDeclarationsAction.run(getWindow(), selection);
  }
  
  /** {@inheritDoc} */
  public void selectionChanged(final IAction ac, final ISelection sel) {
    super.selectionChanged(ac, sel);
    ac.setEnabled(true);
    selection = sel;

    //System.err.println("SEL CHANGED " + selection.getClass());
  }
}
