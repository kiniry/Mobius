package mobius.directVCGen.ui.poview;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;
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
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.ui.ISharedImages;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.console.IOConsole;
import org.eclipse.ui.console.IOConsoleOutputStream;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.progress.UIJob;
import org.osgi.framework.Bundle;


public final class Utils implements IImagesConstants {
  
  static ImageDescriptor descTool;
  
  /** all the images needed by the plugin. */
  private static Image[] images = new Image[NUMBER_IMGS];
  
  static {
    descTool = createImageDescriptor("icons/tool.gif");
    initImages();
  }
  
  /** Default Constructor. */
  private Utils() { }
  
  
  private static void initImages() {
    images[IMG_PROJECT] = 
      getPlatformImage(IDE.SharedImages.IMG_OBJ_PROJECT);
    images[IMG_PROJECT_EMPTY] = 
      getPlatformImage(IDE.SharedImages.IMG_OBJ_PROJECT_CLOSED);
    images[IMG_CLASS] = 
      getJdtImage(ISharedImages.IMG_OBJS_CLASS);
    images[IMG_METHOD] = 
      getJdtImage(ISharedImages.IMG_OBJS_PRIVATE);
    images[IMG_GOAL_SOLVED] = 
      Utils.getJdtImage(ISharedImages.IMG_OBJS_PUBLIC);
    images[IMG_GOAL] = createImage("icons/escjava_problem.gif");    
    images[IMG_LIB] = createImage("icons/coq.gif");
    images[IMG_LIB_RED] = createImage("icons/coq-red.gif"); 
    images[IMG_TOOL] = descTool.createImage();
    images[IMG_OBJS_LIBRARY] = 
      Utils.getJdtImage(ISharedImages.IMG_OBJS_LIBRARY);
    images[IMG_FOLDER] = 
      getPlatformImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FOLDER);
    images[IMG_SRC_FOLDER] = 
      Utils.getJdtImage(ISharedImages.IMG_OBJS_PACKFRAG_ROOT);
    images[IMG_PKG] = 
      Utils.getJdtImage(ISharedImages.IMG_OBJS_PACKAGE);
    images[IMG_DEFAULT] = 
      getPlatformImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FILE);
  
  }
  

  
  /**
   * Returns a standard ok status.
   * @return A standard ok status.
   */
  public static IStatus getOkStatus() {
    return new Status(IStatus.OK, Activator.PLUGIN_ID, IStatus.OK, "", null);
  }
  
  public static ImageDescriptor createImageDescriptor(final String file) {
    final Bundle bundle = Platform.getBundle(Activator.PLUGIN_ID);
    if (bundle == null) {
      System.err.println("Bundle not found!!!");
    }
    final IPath path = new Path(file);
    final URL iconURL = FileLocator.find(bundle, path, null);
    return ImageDescriptor.createFromURL(iconURL);
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
  
  public static  class StreamConnexion extends Thread {
    
    private final InputStream fIn;
    private final OutputStream fOut;
    
    public StreamConnexion(InputStream in, OutputStream out ) {
      fIn = in;
      fOut = out;
    }
  
    public void run() {
      int read;
      try {
        while ((read = fIn.read()) != -1) {
          fOut.write(read);
        } 
      }
      catch (IOException e) {
        e.printStackTrace();
      }
    }
  }

  public static class SystemCallJob extends Job {
  
    private final String[] fArgs;
  
    public SystemCallJob(final String name, final String [] args) {
      super(name);
      fArgs = args;
    }
  
    @Override
    protected IStatus run(final IProgressMonitor monitor) {
      final IOConsole console = Activator.getDefault().getConsole();
      final IOConsoleOutputStream streamOut = console.newOutputStream();
      
      final IOConsoleOutputStream streamErr = console.newOutputStream();
      final IOConsoleOutputStream streamEnd = console.newOutputStream();
      streamErr.setColor(Activator.getDefault().getRed());
      
      final PrintStream out = new PrintStream(streamEnd);
      streamEnd.setColor(Activator.getDefault().getPurple());      
      
      try {
        final Process p = Runtime.getRuntime().exec(fArgs);
        final StreamConnexion connexionOut = 
          new StreamConnexion(p.getInputStream(), streamOut);
        final StreamConnexion connexionErr = 
          new StreamConnexion(p.getErrorStream(), streamErr);
        connexionOut.start();
        connexionErr.start();
        p.waitFor();
      } 
      catch (IOException e) {
        e.printStackTrace(out);
      } 
      catch (InterruptedException e) {
        e.printStackTrace(out);
      }
  
      out.println("\nDone!");
      return getOkStatus();      
    }
  }

  public static Image getPlatformImage(final String id) {
    return PlatformUI.getWorkbench().getSharedImages().getImage(id);
  }
  public static Image getJdtImage(final String id) {
    return JavaUI.getSharedImages().getImage(id);
  }

  public static Image getImage(final int cst) {
    if (0 < cst && cst < NUMBER_IMGS) {
      return images[cst];
    }
    else {
      return images[IMG_DEFAULT];
    }
  }
  
  public static IProject [] getProjects() {
    return ResourcesPlugin.getWorkspace().getRoot().getProjects();
  }
}
