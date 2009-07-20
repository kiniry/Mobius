package mobius.directvcgen.ui.poview.tree;


import mobius.directvcgen.ui.poview.util.ImagesUtils.EImages;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.swt.graphics.Image;

/**
 * A node representing a method of a class. The parent of this node should be
 * a class, btw.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class TargetMethod extends AProofFolder {

  /**
   * Creates a node using the associate folder which represents a method.
   * @param folder a folder representing a method.
   */
  TargetMethod(final IFolder folder) {
    super(folder);
    update();
  }
  
  /** {@inheritDoc} */
  public AWorkspaceElement createChildFromResource(final IResource res) {
    AWorkspaceElement pe = null;
    if ((res instanceof IFile) && res.toString().endsWith(".v")) {
      pe = Factory.createFile((IFile) res);
    }
    return pe;
  }
  
  /** {@inheritDoc} */
  public Image getImage () {
    return  EImages.METHOD.getImg();
  }
}
