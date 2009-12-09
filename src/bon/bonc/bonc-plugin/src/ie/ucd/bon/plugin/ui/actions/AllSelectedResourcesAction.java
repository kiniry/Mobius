package ie.ucd.bon.plugin.ui.actions;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jface.action.IAction;

public abstract class AllSelectedResourcesAction extends AllSelectionsActionDelegate {

  @Override
  protected void run(IAction action, Object[] selectedElements) {
    List<IResource> resources = new ArrayList<IResource>();
    
    for (Object o : selectedElements) {
      if (o instanceof IResource) {
        resources.add((IResource)o);
      } else if (o instanceof IJavaElement) {
        resources.add(((IJavaElement)o).getResource());
      }
    }
    run(action, resources);
  }
  
  protected abstract void run(IAction action, List<IResource> resources);
  
}
