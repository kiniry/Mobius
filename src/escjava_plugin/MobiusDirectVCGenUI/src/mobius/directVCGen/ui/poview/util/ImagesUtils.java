package mobius.directVCGen.ui.poview.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.net.URL;

import mobius.directVCGen.ui.poview.Activator;

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
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.console.IOConsole;
import org.eclipse.ui.console.IOConsoleOutputStream;
import org.eclipse.ui.ide.IDE;
import org.osgi.framework.Bundle;


public final class ImagesUtils implements IImagesConstants {
  
  public static final ImageDescriptor descTool;
  
  /** all the images needed by the plugin. */
  private static Image[] images = new Image[NUMBER_IMGS];
  
  static {
    descTool = createImageDescriptor("icons/tool.gif");
    initImages();
  }
  
  /** Default Constructor. */
  private ImagesUtils() { }
  
  
  
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
      ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_PUBLIC);
    images[IMG_GOAL] = createImage("icons/escjava_problem.gif");    
    images[IMG_LIB] = createImage("icons/coq.gif");
    images[IMG_LIB_RED] = createImage("icons/coq-red.gif"); 
    images[IMG_TOOL] = descTool.createImage();
    images[IMG_OBJS_LIBRARY] = 
      ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_LIBRARY);
    images[IMG_FOLDER] = 
      getPlatformImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FOLDER);
    images[IMG_SRC_FOLDER] = 
      ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_PACKFRAG_ROOT);
    images[IMG_PKG] = 
      ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_PACKAGE);
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
