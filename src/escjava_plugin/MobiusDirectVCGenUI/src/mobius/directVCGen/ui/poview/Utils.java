package mobius.directVCGen.ui.poview;

import java.net.URL;

import mobius.directVCGen.ui.poview.tree.AWorkspaceElement;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.ui.ISharedImages;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.progress.UIJob;
import org.osgi.framework.Bundle;


public final class Utils {
  private static Image imgGoal;
  private static Image imgLib;
  private static Image imgLibRed;
  
  /** Default Constructor. */
  private Utils() { }
  
  /**
   * Returns a standard ok status.
   * @return A standard ok status.
   */
  public static IStatus getOkStatus() {
    return new Status(IStatus.OK, Activator.PLUGIN_ID, IStatus.OK, "", null);
  }
  
  
  public static Image createImage(final String file) {
    final Bundle bundle = Platform.getBundle(Activator.PLUGIN_ID);
    if (bundle == null) {
      System.err.println("Bundle not found!!!");
    }
    final IPath path = new Path(file);
    final URL iconURL = FileLocator.find(bundle, path, null);
    return ImageDescriptor.createFromURL(iconURL).createImage();
  }
  
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
    
    /** {@inheritDoc} */
    public IStatus runInUIThread(final IProgressMonitor monitor) {
      fViewer.refresh(fGoal);
      return Utils.getOkStatus();
    }  
  }
  
  public static Image getPlatformImage(final String id) {
    return PlatformUI.getWorkbench().getSharedImages().getImage(id);
  }
  public static Image getJdtImage(final String id) {
    return JavaUI.getSharedImages().getImage(id);
  }

  public static Image getImage(final int cst) {
    final org.eclipse.ui.ISharedImages im = PlatformUI .getWorkbench().getSharedImages();
    
    switch(cst) {
      case IImagesConstants.IMG_PROJECT:
        return getPlatformImage(IDE.SharedImages.IMG_OBJ_PROJECT);
      case IImagesConstants.IMG_PROJECT_EMPTY:
        return getPlatformImage(IDE.SharedImages.IMG_OBJ_PROJECT_CLOSED);
      case IImagesConstants.IMG_CLASS:
        return getJdtImage(ISharedImages.IMG_OBJS_CLASS);
      case IImagesConstants.IMG_METHOD:
        return getJdtImage(ISharedImages.IMG_OBJS_PRIVATE);
      case IImagesConstants.IMG_GOAL_SOLVED:
        return Utils.getJdtImage(ISharedImages.IMG_OBJS_PUBLIC);
      case IImagesConstants.IMG_GOAL:
        if (imgGoal == null) {
          imgGoal = createImage("icons/escjava_problem.gif");
        }
        return imgGoal;
      case IImagesConstants.IMG_LIB:
        if (imgLib == null) {
          imgLib = createImage("icons/coq.gif");
        }
        return imgLib;
      case IImagesConstants.IMG_LIB_RED:
        if (imgLibRed == null) {
          imgLibRed = createImage("icons/coq-red.gif");
        }
        return imgLibRed;
      case IImagesConstants.IMG_OBJS_LIBRARY:
        return Utils.getJdtImage(ISharedImages.IMG_OBJS_LIBRARY);
      case IImagesConstants.IMG_FOLDER:
        return getPlatformImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FOLDER);
      //case IImagesConstants.IMG_MKFILE:
        //return IDE.getContentType(file);
      case IImagesConstants.IMG_SRC_FOLDER:
        return Utils.getJdtImage(ISharedImages.IMG_OBJS_PACKFRAG_ROOT);
        
      case IImagesConstants.IMG_PKG:
        return Utils.getJdtImage(ISharedImages.IMG_OBJS_PACKAGE);
      case IImagesConstants.IMG_DEFAULT:
      default:
        return getPlatformImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FILE);

    }
  }
  
  public static IProject [] getProjects() {
    return ResourcesPlugin.getWorkspace().getRoot().getProjects();
  }
}
