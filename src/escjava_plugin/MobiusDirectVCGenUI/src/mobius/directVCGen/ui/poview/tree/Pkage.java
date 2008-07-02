package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.swt.graphics.Image;


public class Pkage extends AProofFolder {
  private final int fDepth;
  
  
  Pkage(final IFolder folder, final int depth) {
    super(folder);
    fDepth = depth;
    update();
  }
  
  /** {@inheritDoc} */
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

  /** {@inheritDoc} */
  public Image getImage () {
    return Utils.getImage(IMG_PKG);
  }
}
