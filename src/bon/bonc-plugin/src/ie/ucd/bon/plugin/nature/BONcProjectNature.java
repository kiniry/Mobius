package ie.ucd.bon.plugin.nature;

import ie.ucd.bon.plugin.builder.BONcBuilder;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;

public class BONcProjectNature implements IProjectNature {

  private IProject theProject;

  public void configure() throws CoreException {
    BONcBuilder.addBuilderToProject(theProject);
  }

  public void deconfigure() throws CoreException {
    BONcBuilder.removeBuilderFromProject(theProject);
  }

  public IProject getProject() {
    return theProject;
  }

  public void setProject(IProject project) {
    theProject = project;
  }

}
