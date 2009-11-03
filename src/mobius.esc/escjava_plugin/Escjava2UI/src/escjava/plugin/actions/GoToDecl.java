package escjava.plugin.actions;

import org.eclipse.jface.action.IAction;

import escjava.plugin.WarningDeclarationsAction;

/**
 * This class implements the action that opens and
 * positions an editor on an associated declaration of
 * a marker.
 * 
 * @author David R. Cok
 */
public class GoToDecl extends EscjavaAction {
  /** {@inheritDoc} */
  public final void run(final IAction action) {
    //System.err.println("ACTION " + action.getClass());
    WarningDeclarationsAction.run(getWindow(), getSelection());
  }
}
