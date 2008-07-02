package mobius.directVCGen.ui.poview.tree;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.TreeViewer;

/**
 * A node representing a makefile.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Makefile extends UnknownFile {
  /**
   * Initialize the makefile using the given file.
   * @param file a valid makefile
   */
  Makefile(final IFile file) {
    super(file);
   
  }

  /** {@inheritDoc} */
  public boolean isEvaluateEnabled() {
    return true;
  }
  
  /** {@inheritDoc} */
  public void compile(final TreeViewer viewer) { 
    
  }
}
