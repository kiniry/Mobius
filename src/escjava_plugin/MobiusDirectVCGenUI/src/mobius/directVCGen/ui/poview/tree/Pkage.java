package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.graphics.Image;


public class Pkage extends AProofElement{
  private final IFolder fFolder;
  private final int fDepth;
  
  
  Pkage(final IFolder folder, final int depth) {
    super(folder);
    fFolder = folder;
    fDepth = depth;
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
      final IFolder fold = (IFolder) res;
      pe = Factory.createPackageOrClass(fold, fDepth);
    }
    else if (res instanceof IFile) {
      pe = Factory.createFile((IFile) res);
    }
    return pe;
  }
  
  public String getName() {
    return fFolder.getName();
  }
  
  public Image getImage () {
    return Utils.getImage(IMG_PKG);
  }
}
