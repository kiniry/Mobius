package mobius.directVCGen.ui.poview;

import mobius.directVCGen.ui.poview.util.IImagesConstants;
import mobius.directVCGen.ui.poview.util.ImagesUtils;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IOConsole;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Activator extends AbstractUIPlugin implements IImagesConstants {

  /** The plug-in ID. */
  public static final String PLUGIN_ID = "MobiusDirectVCGenUI";

  /** The shared instance. */
  private static Activator plugin;

  
  
  /**
   * The constructor.
   */
  public Activator() {
    plugin = this;
  }

  /** {@inheritDoc} */
  public void start(final BundleContext context) throws Exception {
    super.start(context);

  }

  /** {@inheritDoc} */
  public void stop(final BundleContext context) throws Exception {
    super.stop(context);
    
  }

  /**
   * Returns the shared instance.
   *
   * @return the shared instance
   */
  public static Activator getDefault() {
    return plugin;
  }
  

}
