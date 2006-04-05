package prover;


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

import prover.preference.PreferencePage;


/**
 * The main plugin class to be used in the desktop.
 */
public class ProverEditorPlugin extends AbstractUIPlugin {

	public static final int SUBVERSION = 1;
	public static final int VERSION = 0;
	public static final int MAJORVERSION = 0;
	private static final String PROVER_EXTENSION_NAMESPACE = "prover.editor";

	//The shared instance.
	private static ProverEditorPlugin plugin;
	
	private IPreferenceStore prefs;
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
		prefs = PlatformUI.getPreferenceStore(); 
		PreferencePage.setDefault(prefs);
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

	public static String getPluginId() {
		return "ProverEditor"; //Platform.PI_RUNTIME;
	}
	

	public void register(IExtension ie) {
		if(ie == null)
			return;
		IConfigurationElement[] ice = ie.getConfigurationElements();
		
		for (int k = 0; k < ice.length; k++) {
			if (ice[k].getName().equals("language")) {
				try {
					new Prover(prefs, ice[k]);
				} catch (Exception ce) {
					System.err.println(ce.getMessage());
				}
			}
		}
	}

	
	

	
	public static ProverEditorPlugin getInstance() {
		return plugin;
	}
	
	
	/**
	 * Preferences for provers
	 * @param language
	 * @return
	 */
	public Prover getProver(String language) {
		Prover pn = (Prover) Prover.get(language);
		return pn;
	}
}
