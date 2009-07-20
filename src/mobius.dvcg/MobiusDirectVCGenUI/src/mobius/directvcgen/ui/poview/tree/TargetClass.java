package mobius.directvcgen.ui.poview.tree;

import mobius.directvcgen.ui.poview.util.ImagesUtils.EImages;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.swt.graphics.Image;

/**
 * A node representing a class (a folder class to be precise).
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class TargetClass extends AProofFolder {

  /**
   * Initialize a class from its corresponding folder.
   * @param folder the folder representing the class
   */
  TargetClass(final IFolder folder) {
    super(folder);
    update();
  }
 
  /** {@inheritDoc} */
  public AWorkspaceElement createChildFromResource(final IResource res) {
    AWorkspaceElement pe = null;
    if (res instanceof IFolder) {
      pe = new TargetMethod((IFolder) res);
    }
    return pe;
  }

  /** {@inheritDoc} */
  public Image getImage () {
    return EImages.CLASS.getImg();
  }
}
