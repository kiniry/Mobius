package escjava.plugin.actions;

import java.util.Iterator;

import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;

import pluginlib.Utils;
import escjava.plugin.EscjavaMarker;

/**
 * This class implements the action that clears
 * EscJava markers.
 * 
 * @author David R. Cok
 */
public class Clear extends EscjavaAction {
	public final void run(final IAction action) {
		try {  // FIXME - continue loop even if exception?
			Iterator i = Utils.getSelectedElements(selection,window).iterator();
			while (i.hasNext()) {
				Object o = i.next();
				if (o instanceof IResource) {
					EscjavaMarker.clearMarkers((IResource)o);
				} else if (o instanceof IJavaElement) {
					IResource r = ((IJavaElement)o).getCorrespondingResource();
					// FIXME - check the behavior of the following if the IJavaElement is smaller than a ocmpilation unit
					if (r != null) EscjavaMarker.clearMarkers(r);
				}
			}
		} catch (Exception e) {
			if (window != null) {
				MessageDialog.openInformation(
						window.getShell(),
						"Escjava Plugin - exception",
						e.toString());
			}			
		}
		return;
		
	}
}