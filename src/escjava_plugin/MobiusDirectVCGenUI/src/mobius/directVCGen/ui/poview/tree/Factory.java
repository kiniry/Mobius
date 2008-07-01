package mobius.directVCGen.ui.poview.tree;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

public class Factory {

  public static WorkspaceElement createCoqFileOrGoal(final IFile f) {
    if (f.getName().startsWith("goal")) {
      return new Goal(f);
    }
    return new LibFile(f);
  }

  public static WorkspaceElement createPackageOrClass(final IFolder folder, 
                                                      final int depth) {
    if (Factory.getDepth(folder) > depth) {
      return new Pkage(folder, depth);
    }
    else {
      return new TargetClass(folder);
    }
  }

  private static int getDepth(final IContainer container) {
    IResource [] rt;
    try {
      rt = container.members();
      if ((rt == null) || (rt.length == 0)) {
        return 0;
      }
    } 
    catch (CoreException e) {
      e.printStackTrace();
      return 0;
    }
    int max = 0;
    for (IResource r: rt) {
      if (r instanceof IContainer) {
        final int res = getDepth((IContainer) r);
        if (res > max) {
          max = res;
        }
      }
    }
    return max + 1;

  }

}
