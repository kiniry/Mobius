package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.util.ImagesUtils;
import mobius.directVCGen.ui.poview.util.ImagesUtils.EImages;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.graphics.Image;


public class Project extends AWorkspaceElement {
  /** the project this objecti is a representation of. */
  private final IProject fProject;
  
  public Project(final IProject project) {
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
