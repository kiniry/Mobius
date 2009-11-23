package mobius.prover.cvc3;

import mobius.prover.Prover;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Cvc3Editor extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "cvc3.editor";

	// The shared instance
	private static Cvc3Editor plugin;
	
	/**
	 * The constructor
	 */
	public Cvc3Editor() {
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
	public static Cvc3Editor getDefault() {
		return plugin;
	}
	public static String getCvc3Location() {
	  Prover p = Prover.get("Cvc3");
	  return p.getTop();
	}
}
