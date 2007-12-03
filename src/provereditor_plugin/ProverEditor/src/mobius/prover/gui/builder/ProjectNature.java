package mobius.prover.gui.builder;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;

/**
 * The nature used to add a tag builder to a project.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ProjectNature implements IProjectNature {
  /** the id of the nature ie: "prover.editor.nature". */
  public static final String NATURE_ID = "prover.editor.nature";
  /** the current project associated with this nature. */
  private IProject fProject;
  
  /** {@inheritDoc} */
  @Override
  public void configure() throws CoreException {
    final IProjectDescription desc = fProject.getDescription();
    final ICommand[] commands = desc.getBuildSpec();

    for (int i = 0; i < commands.length; ++i) {
      if (commands[i].getBuilderName().equals(ProjectBuilder.BUILDER_ID)) {
        return;
      }
    }

    final ICommand[] newCommands = new ICommand[commands.length + 1];
    System.arraycopy(commands, 0, newCommands, 0, commands.length);
    final ICommand command = desc.newCommand();
    command.setBuilderName(ProjectBuilder.BUILDER_ID);
    newCommands[newCommands.length - 1] = command;
    desc.setBuildSpec(newCommands);
    fProject.setDescription(desc, null);

  }

  /** {@inheritDoc} */
  @Override
  public void deconfigure() throws CoreException {
    final IProjectDescription description = getProject().getDescription();
    final ICommand[] commands = description.getBuildSpec();
    for (int i = 0; i < commands.length; ++i) {
      if (commands[i].getBuilderName().equals(ProjectBuilder.BUILDER_ID)) {
        final ICommand[] newCommands = new ICommand[commands.length - 1];
        System.arraycopy(commands, 0, newCommands, 0, i);
        System.arraycopy(commands, i + 1, newCommands, i,
            commands.length - i - 1);
        description.setBuildSpec(newCommands);
        return;
      }
    }

  }

  
  /** {@inheritDoc} */
  @Override
  public IProject getProject() {
    return fProject;
  }
 
  /** {@inheritDoc} */
  @Override
  public void setProject(final IProject project) {
    fProject = project;
  }

}
