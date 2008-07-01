package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.graphics.Image;


public class TargetClass extends AProofElement{
  private final IFolder fFolder;
  
  
  public TargetClass(final IFolder folder) {
    super(folder);
    this.fFolder = folder;
    update();
  }
  
  public void update() {
    IResource[] res = new IResource[0];
    try {
      res = fFolder.members(IResource.NONE);
    } 
    catch (CoreException e) {
      e.printStackTrace();
    }
    update(res);
  }
  
  public AWorkspaceElement createChildFromResource(final IResource res) {
    AWorkspaceElement pe = null;
    if (res instanceof IFolder) {
      pe = new TargetMethod((IFolder) res);
    }
    return pe;
  }
  
  public String getName() {
    return fFolder.getName();
  }
  
  public Image getImage () {
    return Utils.getImage(IMG_CLASS);
  }
}
