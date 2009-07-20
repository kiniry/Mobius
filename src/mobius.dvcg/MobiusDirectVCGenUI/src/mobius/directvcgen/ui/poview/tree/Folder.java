package mobius.directvcgen.ui.poview.tree;

import mobius.directvcgen.ui.poview.util.ImagesUtils.EImages;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.swt.graphics.Image;

/**
 * A node representing a folder.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Folder extends AProofFolder {
  /**
   * Construct a node from the given folder.
   * @param folder the folder associated with this node.
   */
  Folder(final IFolder folder) {
    super(folder);
    update();
  }
  

  /** {@inheritDoc} */
  public AWorkspaceElement createChildFromResource(final IResource res) {
    AWorkspaceElement pe = null;
    final String name = getName();
    if (res instanceof IFolder) {
      final IFolder fold = (IFolder) res;
      if (name.equals("classes") ||
          name.equals("src")) {
        pe = Factory.createPackageOrClass(fold, 0);
      }
      else if (name.equals("vcs")) {
        pe = Factory.createPackageOrClass(fold, 2);
      }
      else {
        pe = new Folder(fold);
      }
    }
    else if (res instanceof IFile) {
      pe = Factory.createFile((IFile) res);
    }
    return pe;
  }
  

  /** {@inheritDoc} */
  public Image getImage () {
    final String name = getName();
    if (name.equals("Formalisation") || 
        name.equals("classes")) {
      return EImages.OBJS_LIBRARY.getImg();
    }
    else if (name.equals("src")) {
      return EImages.SRC_FOLDER.getImg();
    }
    return EImages.FOLDER.getImg();
  }
}
