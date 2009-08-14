package mobius.escjava2;


import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class EscToolsActivator extends AbstractUIPlugin {

  /** The plug-in ID. */
  public static final String PLUGIN_ID = "mobius.escjava2.esctools";

  /** The shared instance. */
  private static EscToolsActivator plugin;

  
  
  /**
   * The constructor.
   */
  public EscToolsActivator() {
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
  public static EscToolsActivator getDefault() {
    return plugin;
  }
  

}

