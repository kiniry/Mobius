package mobius.prover;


import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionDelta;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IRegistryChangeEvent;
import org.eclipse.core.runtime.IRegistryChangeListener;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

import prover.gui.preference.PreferencePage;


/**
 * The main plugin class.
 */
public class ProverEditorPlugin extends AbstractUIPlugin {
	/** the number of minor version */
	public static final int SUBVERSION = 6;
	/** the number of version */
	public static final int VERSION = 1;
	/** the number of the major version */
	public static final int MAJORVERSION = 0;
	
	/** the plugin's extension namespace */
	public static final String PROVER_EXTENSION_NAMESPACE = "prover.editor";
	/** the plugin ID for storage issues */
	public static final String PLUGIN_ID = "ProverEditor";
	
	/** The shared instance. */
	private static ProverEditorPlugin plugin;
	
	/** the current preference store */
	private IPreferenceStore fPrefs;
	
	
	/**
	 * The constructor.
	 */
	public ProverEditorPlugin() {
		plugin = this;
	}

	/**
	 * This method is called upon plug-in activation
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		fPrefs = PlatformUI.getPreferenceStore(); 
		PreferencePage.setDefault(fPrefs);
		PlatformUI.getWorkbench().getExtensionTracker();
		
		if (Platform.getExtensionRegistry() != null) {
			IExtensionPoint[] ipd = 
				Platform.getExtensionRegistry().getExtensionPoints(PROVER_EXTENSION_NAMESPACE);
			Platform.getExtensionRegistry().addRegistryChangeListener(new IRegistryChangeListener(){
				public void registryChanged(IRegistryChangeEvent event) {
					IExtensionDelta [] ied = event.getExtensionDeltas(PROVER_EXTENSION_NAMESPACE);
					for(int i = 0; i < ied.length; i++) {
						register(ied[i].getExtension());
					}
				}
				
			});
			
			for (int i = 0; i < ipd.length; i++) {
				IExtension[] ie = ipd[i].getExtensions();
				for(int j = 0; j < ie.length; j++)
					register(ie[j]);
			}
		}
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
	public static ProverEditorPlugin getDefault() {
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
		return AbstractUIPlugin.imageDescriptorFromPlugin("ProverEditor", path);
	}

	
	
	

	/**
	 * Registers an extension extending the extension point
	 * <code>prover.editor</code> specified.
	 * @param ie the extension to add
	 */
	private void register(IExtension ie) {
		if(ie == null)
			return;
		IConfigurationElement[] ice = ie.getConfigurationElements();
		
		for (int k = 0; k < ice.length; k++) {
			if (ice[k].getName().equals("language")) {
				try {
					new Prover(fPrefs, ice[k]);
				} catch (Exception ce) {
					System.err.println(ce.getMessage());
				}
			}
		}
	}

	
	

	/**
	 * Returns the current instance of the plugin.
	 * @return the current instance or <code>null</code> if
	 * no instance was created yet. 
	 */
	public static ProverEditorPlugin getInstance() {
		return plugin;
	}
	
	
	/**
	 * Preferences for provers
	 * @param language The language we want to have a prover instance
	 * @return the prover instance denominated by the parameter
	 * or <code>null</code> if it wasn't found. 
	 */
	public Prover getProver(String language) {
		Prover pn = (Prover) Prover.get(language);
		return pn;
	}
}
