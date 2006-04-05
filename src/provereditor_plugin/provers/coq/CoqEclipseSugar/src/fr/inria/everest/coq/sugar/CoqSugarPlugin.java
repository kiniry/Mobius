package fr.inria.everest.coq.sugar;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The main plugin class to be used in the desktop.
 */
public class CoqSugarPlugin extends AbstractUIPlugin {

	public static final int SUBVERSION = 2;
	public static final int VERSION = 1;
	public static final int MAJORVERSION = 1;
	//The shared instance.
	private static CoqSugarPlugin plugin;
	
	/**
	 * The constructor.
	 */
	public CoqSugarPlugin() {
		plugin = this;
	}

	/**
	 * This method is called upon plug-in activation
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
	}

	/**
	 * This method is called when the plug-in is stopped
	 */
	public void stop(BundleContext context) throws Exception {
		super.stop(context);
		plugin = null;
	}

	/**
	 * Returns the shared instance.
	 */
	public static CoqSugarPlugin getDefault() {
		return plugin;
	}

	/**
	 * Returns an image descriptor for the image file at the given
	 * plug-in relative path.
	 *
	 * @param path the path
	 * @return the image descriptor
	 */
	public static ImageDescriptor getImageDescriptor(String path) {
		return AbstractUIPlugin.imageDescriptorFromPlugin("CoqEditor", path);
	}

	public static String getPluginId() {
		return "CoqEditor"; //Platform.PI_RUNTIME;
	}
	

}
