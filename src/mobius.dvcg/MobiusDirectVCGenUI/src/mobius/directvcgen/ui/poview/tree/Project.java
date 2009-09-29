package mobius.directvcgen.ui.poview.tree;

import mobius.util.plugin.ImagesUtils.EImages;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.graphics.Image;

/**
 * A node to represent a project. A project is defined by the 
 * associated ressource attached to it.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Project extends AWorkspaceElement {
  /** the project this objecti is a representation of. */
  private final IProject fProject;
  
  /**
   * Creates a new node representing a project.
   * @param project the project from which it is created
   */
  Project(final IProject project) {
    super(project);
    fProject = project;
    update();
  }
  
  /** {@inheritDoc} */
  public void update() {
    final IFolder f = fProject.getFolder("mobius");
    
    IResource[] res = new IResource[0];
    if (f.exists()) {
      try {
        res = f.members(IResource.NONE);
      }
      catch (CoreException e) {
        e.printStackTrace();
      }
    }
    update(res);
  }


  /** {@inheritDoc} */
  public AWorkspaceElement createChildFromResource(final IResource res) {
    AWorkspaceElement pe = null;
    if (res instanceof IFolder) {
      pe = new Folder((IFolder) res);
    }
    if (res instanceof IFile) {
      final IFile f = (IFile) res;
      pe = Factory.createFile(f);

    }
    return pe;
  }
  
  /** {@inheritDoc} */
  public String getName() {
    return fProject.getName();
  }
  
  /** {@inheritDoc} */
  public String toString() {
    return "Project: " + getName();
  }

  /**
   * Returns the project associated with this representation.
   * @return never null
   */
  public IProject getProject() {
    return fProject;
  }
  
  /** {@inheritDoc} */
  public Image getImage () {
    if (this.getChildrenCount() > 0) {
      return EImages.PROJECT.getImg();
    }
    else { 
      return EImages.PROJECT_EMPTY.getImg();
    }
  }

}
