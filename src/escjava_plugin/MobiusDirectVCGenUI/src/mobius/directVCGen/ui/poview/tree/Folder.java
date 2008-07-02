package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.swt.graphics.Image;


public class Folder extends AProofFolder {
  
  public Folder(final IFolder folder) {
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
      return Utils.getImage(IMG_OBJS_LIBRARY);
    }
    else if (name.equals("src")) {
      return Utils.getImage(IMG_SRC_FOLDER);
    }
    return Utils.getImage(IMG_FOLDER);
  }
}
