package mobius.prover.z3;

import mobius.prover.Prover;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Z3Editor extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "z3.editor";

	// The shared instance
	private static Z3Editor plugin;
	
	/**
	 * The constructor
	 */
	public Z3Editor() {
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
	public static Z3Editor getDefault() {
		return plugin;
	}
	public static String getZ3Location() {
	  Prover p = Prover.get("Z3");
	  return p.getTop();
	}
}
