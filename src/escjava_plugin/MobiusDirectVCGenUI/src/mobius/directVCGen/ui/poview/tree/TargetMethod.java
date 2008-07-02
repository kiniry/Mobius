package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.swt.graphics.Image;


public class TargetMethod extends AProofFolder {


  public TargetMethod(final IFolder folder) {
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
    return  Utils.getImage(IMG_METHOD);
  }
}
