package mobius.directvcgen.ui.poview.tree;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;



/**
 * A generic class used to represent in the tree view the nodes
 * of folder class.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public abstract class AProofFolder extends AWorkspaceElement {
  
  /** the folder that this object represents. */
  private final IFolder fFolder;
  
  /**
   * Construct the class from a folder ressource.
   * @param folder a folder which has a disk representation
   */
  public AProofFolder(final IFolder folder) {
    super(folder);
    fFolder = folder;
  } 

  /**
   * Returns the members of the folder which is represented 
   * by this structure.
   * @return an array; the array can be of length 0.
   */
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
