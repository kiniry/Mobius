package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.graphics.Image;


public class Folder extends ProofElement{
	IFolder folder;
	public Folder(IFolder folder) {
		super(folder);
		this.folder = folder;
		update();
	}
	
	public void update() {
		IResource[] res = new IResource[0];
		try {
			res = folder.members(IResource.NONE);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		update(res);
	}
	
	public WorkspaceElement createChildFromResource(IResource res) {
		WorkspaceElement pe = null;
		final String name = folder.getName();
		if(res instanceof IFolder) {
		  IFolder fold = (IFolder) res;
		  if (name.equals("classes") ||
          name.equals("src")) {
        pe = Pkage.createPackageOrClass(fold, 0);
      }
		  else if (name.equals("vcs")) {
        pe = Pkage.createPackageOrClass(fold, 2);
      }
      else {
        pe = new TargetMethod(fold);
      }
		}
		return pe;
	}
	
	public String getName() {
		return folder.getName();
	}
	
	public Image getImage () {
	  final String name = folder.getName();
	  if (name.equals("Formalisation") || 
	      name.equals("classes")) {
	    return Utils.getImage(IMG_OBJS_LIBRARY);
	  }
	  return Utils.getImage(IMG_FOLDER);
	}
}
