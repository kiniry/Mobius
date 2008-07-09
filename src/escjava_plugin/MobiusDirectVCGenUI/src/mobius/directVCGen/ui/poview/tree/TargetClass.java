package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.util.ImagesUtils;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.swt.graphics.Image;


public class TargetClass extends AProofFolder {

  public TargetClass(final IFolder folder) {
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
    return ImagesUtils.getImage(IMG_CLASS);
  }
}
