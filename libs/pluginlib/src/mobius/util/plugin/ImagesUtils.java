package mobius.util.plugin;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;


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


/**
 * A class used to provide utilities for handling images.
 * @author J. Charles (julien.charles@inria.fr)
 */
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
  
  
  /**
   * Create an image descriptor out of a file. It handle errors and everything.
   * 
   * @param file the path to the file. The path is usually the path to a bundle.
   * @return a valid image descriptor or null
   */
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
  
  /**
   * Creates an image from a file.
   * It uses {@link #createImageDescriptor(String)} to handle the 
   * file resolution.
   * 
   * @see
   * #createImageDescriptor(String)
   * @param file the path  to the image
   * @return a valid image or null
   */
  public static Image createImage(final String file) {
    final ImageDescriptor desc = createImageDescriptor(file);
    if (desc == null) {
      return null;
    }
    else {
      return desc.createImage();
    }
  }
  

  /** 
   * A stream connection is a redirection between 2 streams. What is
   * read from the first is written to the second. Since the object
   * is a thread, once it is created a subsequent call to the method 
   * {@link #start()} must be made in order for the connection to be 
   * effective.
   * 
   * @author J. Charles (julien.charles@inria.fr)
   */
  public static  class StreamConnection extends Thread {
    /** the stream from which to read from. */
    private final InputStream fIn;
    /** the stream to which to write. */
    private final OutputStream fOut;
    
    /**
     * Construct a stream connexion.
     * @param in the stream to read from
     * @param out the stream to write to what was read
     */
    public StreamConnection(final InputStream in, final OutputStream out) {
      fIn = in;
      fOut = out;
    }
  
    /** {@inheritDoc} */
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


  /**
   * This method is a helper to get platform images.
   * The image id must be declared in 
   * {@link org.eclipse.ui.IDE.SharedImages}.
   * @param id the id of the image to get.
   * @return an image descriptor or null
   */
  public static ImageDescriptor getPlatformImage(final String id) {
    return PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(id);
  }
  
  /**
   * This method is a helper to get java specific images.
   * The image id must be declared in 
   * {@link org.eclipse.jdt.ui.ISharedImages}.
   * @param id the id of the image to get.
   * @return an image descriptor or null
   */
  public static ImageDescriptor getJdtImage(final String id) {
    return JavaUI.getSharedImages().getImageDescriptor(id);
  }

  /**
   * Returns all the projects of the workspace.
   * @return an array of projects
   * @deprecated use ResourcesPlugin.getWorkspace().getRoot().getProjects()
   * instead
   */
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
    /** an unsolved goal. */
    GOAL,
    /** a solved goal. */
    GOAL_SOLVED,
    /** an uncompiled library. */
    LIB,
    /** a compiled library. */
    LIB_RED,
    /** a library object. */
    OBJS_LIBRARY,
    /** a normal folder. */
    FOLDER,
    /** a source folder. */
    SRC_FOLDER,
    /** a package. */
    PKG,
    /** a makefile. */
    MKFILE;

    /** an image descriptor representing the token. */
    private ImageDescriptor fDesc;
    /** an image taken from the descriptor. */
    private Image fImg;
    
    /**
     * Initialize all the static members of the enum type.
     */
    private static void initImages() {
      PROJECT.fDesc = 
        ImagesUtils.getPlatformImage(IDE.SharedImages.IMG_OBJ_PROJECT);
      PROJECT_EMPTY.fDesc = 
        ImagesUtils.getPlatformImage(IDE.SharedImages.IMG_OBJ_PROJECT_CLOSED);
      CLASS.fDesc = 
        ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_CLASS);
      METHOD.fDesc = 
        ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_PRIVATE);
      GOAL_SOLVED.fDesc = 
        ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_PUBLIC);
      OBJS_LIBRARY.fDesc = 
        ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_LIBRARY);
      FOLDER.fDesc = 
        ImagesUtils.getPlatformImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FOLDER);
      SRC_FOLDER.fDesc = 
        ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_PACKFRAG_ROOT);
      PKG.fDesc = 
        ImagesUtils.getJdtImage(ISharedImages.IMG_OBJS_PACKAGE);
      DEFAULT.fDesc = 
        ImagesUtils.getPlatformImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FILE);
      GOAL.fDesc = ImagesUtils.createImageDescriptor("icons/escjava_problem.gif");    
      LIB.fDesc = ImagesUtils.createImageDescriptor("icons/coq.gif");
      LIB_RED.fDesc = ImagesUtils.createImageDescriptor("icons/coq-red.gif"); 
      TOOL.fDesc = ImagesUtils.createImageDescriptor("icons/tool.gif");
      UNKNOWN.fDesc = DEFAULT.fDesc;
      
      for (EImages img: EImages.values()) {
        if (img.fDesc != null) {
          img.fImg = img.fDesc.createImage();
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
      if (fImg == null) {
        return DEFAULT.fImg;
      }
      return fImg;
    }
    
    /**
     * The image descriptor, can be null.
     * @return a descriptor
     */
    public ImageDescriptor getDescriptor() {
      return fDesc;
    }
  }
}
