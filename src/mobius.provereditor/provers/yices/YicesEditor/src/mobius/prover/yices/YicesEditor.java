package mobius.prover.yices;

import mobius.prover.Prover;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class YicesEditor extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "yices.editor";

	// The shared instance
	private static YicesEditor plugin;
	
	/**
	 * The constructor
	 */
	public YicesEditor() {
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static YicesEditor getDefault() {
		return plugin;
	}
	public static String getSimplifyLocation() {
	  Prover p = Prover.get("Yices");
	  return p.getTop();
	}
}
