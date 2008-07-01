package mobius.directVCGen.ui.poview.tree;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

public class Factory {

  public static WorkspaceElement createCoqFileOrGoal(IFile f) {
    if (f.getName().startsWith("goal")) {
      return new Goal(f);
    }
    return new LibFile(f);
  }

  public static WorkspaceElement createPackageOrClass(IFolder folder, int depth) {
    if (Factory.getDepth(folder) > depth) {
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
