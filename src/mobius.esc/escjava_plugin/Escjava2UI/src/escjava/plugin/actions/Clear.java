package escjava.plugin.actions;

import mobius.util.plugin.Utils;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;

import escjava.plugin.EscjavaMarker;

/**
 * This class implements the action that clears
 * EscJava markers.
 * 
 * @author David R. Cok
 */
public class Clear extends EscjavaAction {
  private static Clear inst;
  
  /** */
  public Clear() {
    super();
    System.out.println(inst);
    inst = this;
  }
  
  /** {@inheritDoc} */
  public final void run(final IAction action) {
    try {  // FIXME - continue loop even if exception?
      
      for (IAdaptable adap: Utils.getSelectedElements(getSelection(), getWindow())) {
        if (adap instanceof IResource) {
          EscjavaMarker.clearMarkers((IResource)adap);
        } 
        else if (adap instanceof IJavaElement) {
          final IResource r = ((IJavaElement)adap).getCorrespondingResource();
          // FIXME - check the behavior of the following 
          // if the IJavaElement is smaller than a ocmpilation unit
          if (r != null) {
            EscjavaMarker.clearMarkers(r);
          }
        }
      }
    } 
    catch (Exception e) {
      if (getWindow() != null) {
        MessageDialog.openInformation(getWindow().getShell(),
                                      "Escjava Plugin - exception",
                                      e.toString());
      }
    }
    return;
  }

  public static Clear getInstance() {
    return inst;
  }
}
