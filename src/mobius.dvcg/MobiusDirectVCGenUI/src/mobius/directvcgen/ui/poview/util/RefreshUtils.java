package mobius.directvcgen.ui.poview.util;

import mobius.directvcgen.ui.poview.tree.AWorkspaceElement;
import mobius.util.plugin.ImagesUtils;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.SWTException;
import org.eclipse.ui.progress.UIJob;

/**
 * This utility class is used to creates jobs to refresh the tree view.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class RefreshUtils {
  
  /** */
  private RefreshUtils() { }
  
  /**
   * Creates an asynchronous job to refresh the tree view.
   * @param viewer the viewer to refresh
   * @param goal the specific target goal which has been modified
   */
  public static void refreshTree(final TreeViewer viewer, final AWorkspaceElement goal) {
    final UIJob job = new RefreshJob(viewer, goal);
    job.schedule();
  }
  
  /**
   * Creates an asynchronous job to refresh the tree view.
   * @param viewer the viewer to refresh
   */
  public static void refreshTree(final TreeViewer viewer) {
    final UIJob job = new RefreshJob(viewer);
    job.schedule();
  }
  
  /**
   * Creates an asynchronous job to refresh a specific resource which has
   * had its state changed on the disk.
   * @param res the resource to update.
   */
  public static void refreshResource(final IResource res) {
    final UIJob job = new RefreshResourceJob(res);
    job.schedule();
  }
  
  /**
   * A job to refresh a specific ressource if it states has changed
   * on the disk.
   * 
   * @author J. Charles (julien.charles@inria.fr)
   */
  private static class RefreshResourceJob extends UIJob {
    /** the resource which has to be refreshed. */
    private final IResource fRes;

    /**
     * Construct a job to refresh a resource.
     * @param res the resource to update.
     */
    public RefreshResourceJob(final IResource res) {
      super("Updating resource");
      fRes = res;
    }
    

    /** {@inheritDoc} */
    public IStatus runInUIThread(final IProgressMonitor monitor) {
      try {
        fRes.refreshLocal(IResource.DEPTH_INFINITE, monitor);
      }
      catch (CoreException e) {
        e.printStackTrace();
      }
      return ImagesUtils.getOkStatus();
    }  
  }
  
  /**
   * A job to refresh a specific viewer if one of its elements has
   * been modified.
   * 
   * @author J. Charles (julien.charles@inria.fr)
   */
  private static class RefreshJob extends UIJob {
    /** the viewer which will have to be refreshed. */
    private final TreeViewer fViewer;
    /** the element which has to be refreshed. */
    private final AWorkspaceElement fElem;
    
    /**
     * Build a refresh job, which refresh the viewer, starting from the given
     * element.
     * @param viewer the viewer to refresh
     * @param elem the node which has to be updated
     */
    public RefreshJob(final TreeViewer viewer, final AWorkspaceElement elem) {
      super("Updating view");
      assert (viewer != null);
      fViewer = viewer;
      fElem = elem;

    }
    
    /**
     * Create a refresh job bound to refresh the whole viewer.
     * @param viewer the viewer to refresh
     */
    public RefreshJob(final TreeViewer viewer) {
      this(viewer, null);
    }

    /** {@inheritDoc} */
    public IStatus runInUIThread(final IProgressMonitor monitor) {
      try {
        if (fElem != null) {
          fViewer.refresh(fElem);
          fViewer.update(fElem, null);
        }
        else {
          fViewer.refresh();
        }
      }
      catch (SWTException e) {
        if (e.code != SWT.ERROR_WIDGET_DISPOSED) {
          throw e; // le concept de la patate chaude
        }
      }
      return ImagesUtils.getOkStatus();
    }  
  }
}
