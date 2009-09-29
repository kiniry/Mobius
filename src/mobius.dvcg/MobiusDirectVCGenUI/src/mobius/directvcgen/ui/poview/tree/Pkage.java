package mobius.directvcgen.ui.poview.tree;

import mobius.util.plugin.ImagesUtils.EImages;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.swt.graphics.Image;

/**
 * A node that represents a Java package. There is a depth associated to
 * it, which gives the min depth of children it should have.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Pkage extends AProofFolder {
  /** the depth of folders that are considered as class/methods/goals. */
  private final int fDepth;
  
  /**
   * Build a node which represents a package entry.
   * @param folder the folder which represents a package.
   * @param depth the depth up until which the folder should be a Class...
   */
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
    return EImages.PKG.getImg();
  }
}
