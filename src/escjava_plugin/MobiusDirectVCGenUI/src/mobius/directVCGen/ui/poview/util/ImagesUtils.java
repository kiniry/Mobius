package mobius.directVCGen.ui.poview.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;

import mobius.directVCGen.ui.poview.Activator;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.ui.ISharedImages;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
import org.osgi.framework.Bundle;


public final class ImagesUtils {
  
  /** Default Constructor. */
  private ImagesUtils() { }
  
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
      return null;
    }
    final IPath path = new Path(file);
    final URL iconURL = FileLocator.find(bundle, path, null);
    return ImageDescriptor.createFromURL(iconURL);
  }
  
  public static Image createImage(final String file) {
    final ImageDescriptor desc = createImageDescriptor(file);
    if (desc == null) {
      return null;
    }
    else {
      return desc.createImage();
    }
  }
  

  
  public static  class StreamConnexion extends Thread {
    
    private final InputStream fIn;
    private final OutputStream fOut;
    
    public StreamConnexion(final InputStream in, final OutputStream out ) {
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


  public static ImageDescriptor getPlatformImage(final String id) {
    return PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(id);
  }
  public static ImageDescriptor getJdtImage(final String id) {
    return JavaUI.getSharedImages().getImageDescriptor(id);
  }

  
  public static IProject [] getProjects() {
    return ResourcesPlugin.getWorkspace().getRoot().getProjects();
  }
  
  /** The constants used to handle the images for the tree nodes. */
  public enum EImages {
    /** the default image. */
    DEFAULT,
    /** the image for an unknown file. */
    UNKNOWN,
    /** the image for an unknown file. */
    TOOL,
    /** the eclipse symbol for methods. */
    METHOD, 
    /** the eclipse symbol for classes. */
    CLASS,
    /** a project (an open folder). */
    PROJECT, 
    /** an empty project (a closed folder). */
    PROJECT_EMPTY, 
    GOAL,
    GOAL_SOLVED,
    LIB,
    LIB_RED,
    OBJS_LIBRARY,
    FOLDER,
    SRC_FOLDER,
    PKG,
    MKFILE;

    private Image img;
    private ImageDescriptor desc;
    
    private static void initImages() {
      PROJECT.desc = 
        ImagesUtils.getPlatformImage(IDE.SharedImages.IMG_OBJ_PROJECT);
      PROJECT_EMPTY.desc = 
        ImagesUtils.getPlatformImage(IDE.SharedImages.IMG_OBJ_PROJECT_CLOSED);
      CLASS.desc = 
        ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_CLASS);
      METHOD.desc = 
        ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_PRIVATE);
      GOAL_SOLVED.desc = 
        ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_PUBLIC);
      OBJS_LIBRARY.desc = 
        ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_LIBRARY);
      FOLDER.desc = 
        ImagesUtils.getPlatformImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FOLDER);
      SRC_FOLDER.desc = 
        ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_PACKFRAG_ROOT);
      PKG.desc = 
        ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_PACKAGE);
      DEFAULT.desc = 
        ImagesUtils.getPlatformImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FILE);
      GOAL.desc = ImagesUtils.createImageDescriptor("icons/escjava_problem.gif");    
      LIB.desc = ImagesUtils.createImageDescriptor("icons/coq.gif");
      LIB_RED.desc = ImagesUtils.createImageDescriptor("icons/coq-red.gif"); 
      TOOL.desc = ImagesUtils.createImageDescriptor("icons/tool.gif");
      UNKNOWN.desc = DEFAULT.desc;
      
      for (EImages img: EImages.values()) {
        if (img.desc != null) {
          img.img = img.desc.createImage();
        }
      }
    }
    
    static {
      initImages();
    }

    /**
     * Returns the image associated with the constant.
     * @return an image or the default image
     */
    public Image getImg() {
      if (img == null) {
        return DEFAULT.img;
      }
      return img;
    }
    
    /**
     * The image descriptor, can be null.
     * @return a descriptor
     */
    public ImageDescriptor getDescriptor() {
      return desc;
    }
  }
}
