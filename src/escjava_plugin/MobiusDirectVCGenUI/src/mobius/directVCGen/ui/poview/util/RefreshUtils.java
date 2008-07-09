package mobius.directVCGen.ui.poview.util;

import mobius.directVCGen.ui.poview.tree.AWorkspaceElement;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.progress.UIJob;

public class RefreshUtils {
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
  

  public static void refreshResource(IResource res) {
    final UIJob job = new RefreshResourceJob(res);
    job.schedule();
  }
  /**
   * A job to refresh a specific viewer if one of its goal has
   * been modified.
   * 
   * @author J. Charles (julien.charles@inria.fr)
   */
  private static class RefreshResourceJob extends UIJob {
    
    private final IResource fRes;

    
    public RefreshResourceJob(final IResource res) {
      super("Updating view");
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
   * A job to refresh a specific viewer if one of its goal has
   * been modified.
   * 
   * @author J. Charles (julien.charles@inria.fr)
   */
  private static class RefreshJob extends UIJob {
    
    private final TreeViewer fViewer;
    private final AWorkspaceElement fGoal;
    
    public RefreshJob(final TreeViewer viewer, final AWorkspaceElement goal) {
      super("Updating view");
      fViewer = viewer;
      fGoal = goal;
    }
    
    public RefreshJob(TreeViewer viewer) {
      this(viewer, null);
    }

    /** {@inheritDoc} */
    public IStatus runInUIThread(final IProgressMonitor monitor) {
      if (fGoal != null) {
        fViewer.refresh(fGoal);
      }
      else {
        fViewer.refresh();
      }
      return ImagesUtils.getOkStatus();
    }  
  }
}
