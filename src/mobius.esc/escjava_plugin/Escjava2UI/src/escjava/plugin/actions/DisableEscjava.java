package escjava.plugin.actions;

import java.util.Date;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.action.IAction;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PlatformUI;

import pluginlib.Log;
import pluginlib.Utils;
import escjava.plugin.EscjavaPlugin;

/**
 * This action disables the JML nature on the selected projects.
 * 
 * @author David Cok
 *
 */
public class DisableEscjava extends EscjavaAction {
	// This is all done in the UI thread with no progress
	// FIXME - is it fast enough?

	public final void run(final IAction action) {
		try {
			Map map = Utils.sortByProject(Utils.getSelectedElements(selection,window));
			Iterator i = map.keySet().iterator();
			while (i.hasNext()) {
				IProject p = ((IJavaProject)i.next()).getProject();
				EscjavaPlugin.getPlugin().removeEscjavaAutocheckNature(p);
			}
			// Update the decorators in the UI thread
			Display.getDefault().syncExec(new java.lang.Runnable() {
			  public void run() {
			    PlatformUI.getWorkbench().getDecoratorManager().update(
			      EscjavaPlugin.PLUGIN_ID + ".ESCDecoratorA");
			  }
			});
		} catch (Exception e) {
			Log.errorlog("Failed to disable Esc/Java nature",e);
		}
		if (Log.on) Log.log("Completed Disable Esc/Java operation " + (new Date()));
	}
}