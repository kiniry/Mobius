package umbra;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The main plugin class to be used in the desktop.
 */
public class UmbraPlugin extends AbstractUIPlugin {

    /**
     * The shared instance of the plugin.
     */
    private static UmbraPlugin plugin;
    
    /**
     * The constructor which shares the instance.
     */
    public UmbraPlugin() {
        plugin = this;
    }

    /**
     * This method is called upon plug-in activation.
     * 
     * @param context the context from which the bundle for this plug-in is
     * extracted
     * @throws Exception if this method fails to shut down this plug-in
     */
    public void start(final BundleContext context) throws Exception {
        super.start(context);
    }

    /**
     * This method is called when the plug-in is stopped.
     * 
     * @param context the context from which the bundle for this plug-in is
     * extracted
     * @throws Exception if this method fails to shut down this plug-in
     */
    public void stop(final BundleContext context) throws Exception {
        super.stop(context);
        plugin = null;
    }

    /**
     * Returns the shared instance.
     * 
     * @return the only instance of the Umbra plugin in the system.
     */
    public static UmbraPlugin getDefault() {
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
        return AbstractUIPlugin.imageDescriptorFromPlugin("umbra", path);
    }
}
