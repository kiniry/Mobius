package mobius.directVCGen.ui.poview.tree;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

public final class Factory {

  /** default constructor.  */
  private Factory() { }
  
  
  /**
   * Creates a node representing a file. It can be a coq file,
   * a goal, or another file type. If it is a compiled Coq file
   * ignores it. 
   * @param f the file to represent as a node.
   * @return a node
   */
  public static AWorkspaceElement createFile(final IFile f) {
    final AWorkspaceElement res;
    if (f.getName().endsWith(".v")) {
      
      if (f.getName().startsWith("goal")) {
        res = new Goal(f);
      }
      else {
        res = new LibFile(f);
      }
    }
    else if (f.getName().endsWith(".vo")) {
      res = null;
    }    
    else {
      res = new UnknownFile(f);
    }
    return res;
  }

  public static AWorkspaceElement createPackageOrClass(final IFolder folder, 
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
