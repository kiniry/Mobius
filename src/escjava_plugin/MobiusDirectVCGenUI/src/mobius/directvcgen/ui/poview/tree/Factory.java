package mobius.directvcgen.ui.poview.tree;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;


/**
 * This class is used to create the tree node in a factory way:
 * instead of calling explicitly the constructors, it is suggested
 * to go through this lib.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
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
    else if (f.getName().equals("Makefile")) {
      res = new Makefile(f);
    }
    else {
      res = new UnknownFile(f);
    }
    return res;
  }

  /**
   * Create a package or a class depending on the depth. If the there is 
   * more depth lasting in the folder thant the depth mentionned by the parameter
   * depth, a package is created otherwise a class is created.
   * @param folder the resource to create a node from
   * @param depth the depth by which to trigger the class node creation instead of
   * package node creation
   * @return a valid tree node, representing the ressource given by folder.
   */
  public static AWorkspaceElement createPackageOrClass(final IFolder folder, 
                                                      final int depth) {
    if (Factory.getDepth(folder) > depth) {
      return new Pkage(folder, depth);
    }
    else {
      return new TargetClass(folder);
    }
  }

  /**
   * Returns the max depth of the resource tree, from the given container.
   * @param node the node from which to start.
   * @return a depth, superior or equal zero
   */
  private static int getDepth(final IContainer node) {
    IResource [] rt;
    try {
      rt = node.members();
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
