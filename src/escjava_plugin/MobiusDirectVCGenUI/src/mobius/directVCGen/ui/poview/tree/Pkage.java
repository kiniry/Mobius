package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.graphics.Image;


public class Pkage extends ProofElement{
	private final IFolder fFolder;
	private final int fDepth;
	private Pkage(final IFolder folder, final int depth) {
		super(folder);
		fFolder = folder;
		fDepth = depth;
		update();
	}
	
	public void update() {
		IResource[] res = new IResource[0];
		try {
			res = fFolder.members(IResource.NONE);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		update(res);
	}
	
	public WorkspaceElement createChildFromResource(IResource res) {
		WorkspaceElement pe = null;
		final String name = fFolder.getName();
		if(res instanceof IFolder) {
		  IFolder fold = (IFolder) res;
		  pe = createPackageOrClass(fold, fDepth);
		}
		else if (res instanceof IFile){
		  pe = LibFile.createCoqFileOrGoal((IFile) res);
		}
		return pe;
	}
	
	public String getName() {
		return fFolder.getName();
	}
	
	public Image getImage () {
	  return Utils.getImage(IMG_PKG);
	}
	
	public static WorkspaceElement createPackageOrClass(IFolder folder, int depth) {
	  if (getDepth(folder) > depth) {
	    return new Pkage(folder, depth);
	  }
	  else {
	    return new TargetClass(folder);
	  }
	}

  private static int getDepth(final IFolder folder) {
    int count = 0;
    try {
      
      IResource [] rt = folder.members();
      while ((rt != null) && (rt.length != 0)) {
        count ++;
        
        IContainer cont = null;
        for (IResource r: rt) {
          if (r instanceof IContainer) {
            cont = (IContainer) r;
            break;
          }
        }
        if (cont == null) {
          return count;
        }
        rt = cont.members();
        
      } 

    } catch (CoreException e) {
      e.printStackTrace();
    }
    return count;
  }
}
