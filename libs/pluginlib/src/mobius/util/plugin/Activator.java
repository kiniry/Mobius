package mobius.util.plugin;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

public class Activator extends AbstractUIPlugin {
  /** The plug-in ID. */
  public static final String PLUGIN_ID = "mobius.pluginlib";

  /** The shared instance. */
  private static Activator plugin;


  /** {@inheritDoc} */
  public void start(final BundleContext context) throws Exception {
    super.start(context);
    plugin = this;
  }

  /** {@inheritDoc} */
  public void stop(final BundleContext context) throws Exception {
    plugin = null;
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
