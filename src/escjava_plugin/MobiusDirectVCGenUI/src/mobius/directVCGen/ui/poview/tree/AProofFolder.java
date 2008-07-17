package mobius.directVCGen.ui.poview.tree;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

public abstract class AProofFolder extends AWorkspaceElement {
  
  /** the folder that this object represents. */
  private final IFolder fFolder;
  
  
  public AProofFolder(final IFolder folder) {
    super(folder);
    fFolder = folder;
  } 

  public IResource[] getFolderMembers() {
    try {
      return fFolder.members(IResource.NONE);
    } 
    catch (CoreException e) {
      e.printStackTrace();
    }
    return new IResource[0];
  }
  
  /** 
   * The name of the object, the folder name.
   * @return a valid string. 
   */
  public final String getName() {
    return fFolder.getName();
  }
  
  /** {@inheritDoc} */
  public final void update() {
    final IResource[] res = getFolderMembers();
    update(res);
  }
}
