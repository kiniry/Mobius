package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.graphics.Image;


public class Project extends AProofElement {
  private final IProject fProject;
  
  public Project(final IProject project) {
    super(project);
    fProject = project;
    update();
  }
  
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



  public AWorkspaceElement createChildFromResource(final IResource res) {
    AWorkspaceElement pe = null;
    if (res instanceof IFolder) {
      pe = new Folder((IFolder) res);
    }
    if (res instanceof IFile) {
      final IFile f = (IFile) res;
      if (!f.getName().endsWith(".v")) {
        return null;
      }
      pe = Factory.createFile(f);

    }
    return pe;
  }
  
  public String getName() {
    return fProject.getName();
  }
  public String toString() {
    return "Project: " + getName();
  }

  public IProject getProject() {
    return fProject;
  }
  public Image getImage () {
    if (this.getChildrenCount() > 0) {
      return Utils.getImage(IMG_PROJECT);
    }
    else { 
      return Utils.getImage(IMG_PROJECT_EMPTY);
    }
  }

}
