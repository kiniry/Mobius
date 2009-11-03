package escjava.plugin.actions;

import java.util.Date;

import mobius.util.plugin.Log;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.action.IAction;

import escjava.plugin.AutoCheckBuilder;

/**
 * @author David Cok
 *
 * Implements an action that removes selected files from
 * the RAC enabled list.
 */
public class DisableESC extends ESC {
  /** {@inheritDoc} */
  public void action(final IResource resource) {
    AutoCheckBuilder.remove(resource);
  }
  
  /** {@inheritDoc} */
  public void run(final IAction action) {
    super.run(action);
    if (Log.on) {
      Log.log("Completed Disable Esc/Java action " + (new Date().toString()));
    }
  }
}
