package mobius.directvcgen.ui.poview.tree;



import mobius.util.plugin.ConsoleUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.jobs.Job;
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
    
    final IPath path = getFile().getLocation().removeLastSegments(1);
    final String [] args = {"/bin/sh", "-c",
                            "cd " + path  + "; " + "make"};

    final Job j = new ConsoleUtils.SystemCallJob("Make", args);
    j.schedule();    
  }
}
