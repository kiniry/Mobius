package ie.ucd.bon.plugin.builder;

import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

public class BONcBuilder extends IncrementalProjectBuilder {


  protected IProject[] build(int kind, Map args, IProgressMonitor monitor)
      throws CoreException {

    if (kind == IncrementalProjectBuilder.FULL_BUILD) {
      System.out.println("Full build");
    } else if (kind == IncrementalProjectBuilder.INCREMENTAL_BUILD) {
      System.out.println("Incremental Build");
    } else if (kind == IncrementalProjectBuilder.AUTO_BUILD) {
      System.out.println("Auto Build");
    }
    
    IResource[] resources = getProject().members();
    for (IResource resource : resources) {
      System.out.println("Resource: " + resource.getFullPath());
    }
    
    return null;
  }

}
