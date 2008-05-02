package mobius.prover.gui.popup;


import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;
import java.io.PrintStream;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import mobius.prover.gui.jobs.ProverStatus;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.progress.UIJob;


/**
 * The action triggering a compilation deed.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AddToLoadPath implements IActionDelegate {

  /** The current selection in the workbench. */
  private IStructuredSelection fSel;
  
  /** {@inheritDoc} */
  public void run(final IAction action) {
    if (fSel == null) {
      return;
    }
    if (!(fSel.getFirstElement() instanceof IFolder)) {
      return;
    }
    final IFolder f = (IFolder) fSel.getFirstElement();
    
    final String folder =  f.getProjectRelativePath().toString();
    
    final Job job = new AddingJob(f.getProject(), folder);
    job.schedule();
  }

  /** {@inheritDoc} */
  public void selectionChanged(final IAction action, 
                               final ISelection selection) {
    if (selection instanceof IStructuredSelection) {
      fSel = (IStructuredSelection) selection;
      final Object o = fSel.getFirstElement();
      if (o instanceof IFolder) {
        //IFolder f = (IFolder) o;
        action.setEnabled(true);
        return;
      }
    }
    action.setEnabled(false);
  }
  

  /**
   * This class represents a job used to add a path to the load path list.
   * @author J. Charles (julien.charles@inria.fr)
   */
  public class AddingJob extends Job {
    /** the path of the project. */
    private final String fRoot;
    /** the folder to add, relative to the project. */
    private final String fFolder;
    /** the current project. */
    private final IProject fProject;
    
    
    /**
     * Creates a job used to add a load path to a project.
     * @param project the project in which the folder is
     * @param folder the folder to add
     */
    public AddingJob(final IProject project, final String folder) {
      super("Adding path to ProverEditor paths...");
      fProject = project;
      fRoot = fProject.getLocation().toString();
      fFolder = folder;
    }

    /** {@inheritDoc} */
    @Override
    protected IStatus run(final IProgressMonitor monitor) {
      final File f = new File(fRoot + File.separator + ".prover_paths");
      //System.out.println (f);
      try {
        final Set<String> paths = getPaths(f); 
        paths.add(fFolder);
        writePaths(f, paths);
      }
      catch (IOException e) {
        return ProverStatus.getErrorStatus("Problem writing paths", e);
      }
      final UIJob uij = new UIJob("Updating") {

        public IStatus runInUIThread(final IProgressMonitor monitor) {
          try {
            fProject.refreshLocal(IResource.DEPTH_ONE, monitor);
          } 
          catch (CoreException e) {
            // we don't care for errors
            return ProverStatus.getOkStatus();
          }
          return ProverStatus.getOkStatus();
        }
        
      };
      uij.schedule();
      return ProverStatus.getOkStatus();
    }  
  }
  
  /**
   * Returns the set of relative paths for a given project.
   * @param project the absolute path to the project to get the load path from
   * @return the set of load path
   * @throws IOException if the reading of the path fails
   */
  public static Set<String> getPaths(final String project) throws IOException {
    final File f = new File(project + File.separator + ".prover_paths");
    return getPaths(f);
  }

  /**
   * Returns the set of absolute paths contained in the given file.
   * @param f the file containing the paths
   * @return the set of load path
   * @throws IOException if the reading of the file fails
   */
  private static Set<String> getPaths(final File f) throws IOException {
    final Set<String> hs = new HashSet<String>();
    if (!f.exists()) {
      return hs;
    }
    final LineNumberReader lnr = new LineNumberReader(new FileReader(f));
    String s;
    while ((s = lnr.readLine()) != null) {
      hs.add(s);
    }
    lnr.close();
    return hs;
  }

  /**
   * Write the LoadPath to disk.
   * @param f the file in which to write the paths
   * @param paths the set of path to write
   * @throws IOException if the writing of the file fails
   */
  private static void writePaths(final File f, final Set<String> paths) throws IOException {
    final PrintStream ps = new PrintStream(new FileOutputStream(f));
    final Iterator<String> iter = paths.iterator();
    while (iter.hasNext()) {
      ps.println(iter.next().toString());
    }
    ps.close();
  }

  /**
   * Returns the set of absolute path of the load path.
   * @param project the project from which the path are taken from
   * @return a set of absolute path
   * @throws IOException if the path file cannot be read
   */
  public static Set<String> getAbsolutePaths(final IProject project) throws IOException {
    final String projPath = project.getLocation().toString();
    final Set<String> s = getPaths(projPath);
    final Set<String> res = new HashSet<String>();
    for (String path: s) {
      res.add(projPath + File.separator + path);
    }
 
    return res;
  }  
  
}
