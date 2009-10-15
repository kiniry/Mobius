package escjava.plugin.actions;

import java.util.Collection;
import java.util.Date;
import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.action.IAction;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PlatformUI;

import pluginlib.Log;
import pluginlib.Utils;
import escjava.plugin.EscjavaPlugin;

/**
 * This action enables the JML nature on the selected projects.
 * 
 * @author David Cok
 *
 */
public class EnableEscjava extends EscjavaAction {
  // This is all done in the UI thread with no progress
  // FIXME - is it fast enough?
  /** {@inheritDoc} */
  public final void run(final IAction action) {
    try {
      final Map<IJavaProject, Collection<IAdaptable>>  map = 
        Utils.sortByProject(Utils.getSelectedElements(selection, window));
      for (IJavaProject proj: map.keySet()) {
        final IProject p = proj.getProject();
        EscjavaPlugin.getPlugin().addEscjavaAutocheckNature(p);
      }
      // Update the decorators in the UI thread
      Display.getDefault().syncExec(new java.lang.Runnable() {
        public void run() {
          PlatformUI.getWorkbench().getDecoratorManager().update(
            EscjavaPlugin.PLUGIN_ID + ".ESCDecoratorA");
        }
      });
    }
    catch (CoreException e) {
      Log.errorlog("Failed to enable Esc/Java nature; classpath:" + 
                   System.getProperty("java.class.path"), e);
    }
    if (Log.on) {
      Log.log("Completed Enable Esc/Java operation " + (new Date()));
    }
  }
}