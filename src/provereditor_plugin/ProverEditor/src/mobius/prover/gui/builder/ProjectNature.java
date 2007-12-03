package mobius.prover.gui.builder;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;

/**
 * The nature used to add a tag builder to a project.
 * @author J. Charles
 */
public class ProjectNature implements IProjectNature {
  /** the id of the nature ie: "prover.editor.nature" */
  public static final String NATURE_ID = "prover.editor.nature";
  
  
  /**
   * Configure the nature; add the builder to the project.
   */
  /*
   * (non-Javadoc)
   * @see org.eclipse.core.resources.IProjectNature#configure()
   */
  public void configure() throws CoreException {
    IProjectDescription desc = fProject.getDescription();
    ICommand[] commands = desc.getBuildSpec();

    for (int i = 0; i < commands.length; ++i) {
      if (commands[i].getBuilderName().equals(ProjectBuilder.BUILDER_ID)) {
        return;
      }
    }

    ICommand[] newCommands = new ICommand[commands.length + 1];
    System.arraycopy(commands, 0, newCommands, 0, commands.length);
    ICommand command = desc.newCommand();
    command.setBuilderName(ProjectBuilder.BUILDER_ID);
    newCommands[newCommands.length - 1] = command;
    desc.setBuildSpec(newCommands);
    fProject.setDescription(desc, null);

  }

  /**
   * Deconfigure the nature; remove the builder from the project.
   */
  /*
   * (non-Javadoc)
   * @see org.eclipse.core.resources.IProjectNature#deconfigure()
   */
  public void deconfigure() throws CoreException {
    IProjectDescription description = getProject().getDescription();
    ICommand[] commands = description.getBuildSpec();
    for (int i = 0; i < commands.length; ++i) {
      if (commands[i].getBuilderName().equals(ProjectBuilder.BUILDER_ID)) {
        ICommand[] newCommands = new ICommand[commands.length - 1];
        System.arraycopy(commands, 0, newCommands, 0, i);
        System.arraycopy(commands, i + 1, newCommands, i,
            commands.length - i - 1);
        description.setBuildSpec(newCommands);
        return;
      }
    }

  }
  /** the current project associated with this nature */
  private IProject fProject = null;
  
  /*
   * (non-Javadoc)
   * @see org.eclipse.core.resources.IProjectNature#getProject()
   */
  public IProject getProject() {
    return fProject;
  }

  /*
   * (non-Javadoc)
   * @see org.eclipse.core.resources.IProjectNature#setProject(org.eclipse.core.resources.IProject)
   */
  public void setProject(IProject project) {
    fProject =project;
  }

}
