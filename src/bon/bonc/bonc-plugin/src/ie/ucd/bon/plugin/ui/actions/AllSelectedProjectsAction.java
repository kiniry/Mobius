package ie.ucd.bon.plugin.ui.actions;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.action.IAction;

public abstract class AllSelectedProjectsAction extends AllSelectionsActionDelegate {

  @Override
  protected void run(IAction action, Object[] selectedElements) {
    List<IProject> projects = new ArrayList<IProject>();
    
    for (Object o : selectedElements) {
      if (o instanceof IProject) {
        projects.add((IProject)o);
      } else if (o instanceof IJavaProject) {
        projects.add(((IJavaProject)o).getProject());
      }
    }
    run(action, projects);
  }
  
  protected abstract void run(IAction action, List<IProject> resources);

}
