package fr.inria.everest.coq.editor;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The main plugin class to be used in the desktop.
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CoqEditorPlugin extends AbstractUIPlugin {

  /** The shared instance. */
  private static CoqEditorPlugin plugin;
  
  /**
   * The constructor.
   */
  public CoqEditorPlugin() {
    plugin = this;
  }

  /** {@inheritDoc} */
  @Override
  public void start(final BundleContext context) throws Exception {
    super.start(context);
  }

  /** {@inheritDoc} */
  @Override
  public void stop(final BundleContext context) throws Exception {
    super.stop(context);
    plugin = null;
  }

  /**
   * @return the shared instance.
   */
  public static CoqEditorPlugin getDefault() {
    return plugin;
  }

  /**
   * Returns an image descriptor for the image file at the given
   * plug-in relative path.
   *
   * @param path the path
   * @return the image descriptor
   */
  public static ImageDescriptor getImageDescriptor(final String path) {
    return AbstractUIPlugin.imageDescriptorFromPlugin("CoqEditor", path);
  }
}
