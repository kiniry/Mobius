package ie.ucd.bon.plugin;

import freemarker.template.Configuration;
import ie.ucd.bon.API;
import ie.ucd.bon.plugin.editor.BONCodeScanner;
import ie.ucd.bon.plugin.editor.BONColourProvider;
import ie.ucd.bon.plugin.util.EclipsePluginInputStreamProvider;
import ie.ucd.bon.plugin.util.EclipsePluginURLTemplateLoader;
import ie.ucd.bon.plugin.util.EclipsePluginVersionProvider;
import ie.ucd.bon.printer.template.FreeMarkerTemplate;
import ie.ucd.bon.util.FileUtil;
import ie.ucd.bon.util.StringUtil;

import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class BONPlugin extends AbstractUIPlugin {

  // The plug-in ID
	public static final String PLUGIN_ID = "ie.ucd.bon.plugin";
	public static final String NATURE_ID = PLUGIN_ID + ".boncnature";
	
	// The shared instance
	private static BONPlugin plugin;
	
	//Singletons
	private BONColourProvider fColorProvider;
	private BONCodeScanner fCodeScanner;
	
	/**
	 * The constructor
	 */
	public BONPlugin() {
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		
		FileUtil.inputStreamProvider = new EclipsePluginInputStreamProvider(API.PLUGIN_ID);
		StringUtil.versionProvider = new EclipsePluginVersionProvider(API.PLUGIN_ID);
		Configuration config = new Configuration();
		config.setTemplateLoader(new EclipsePluginURLTemplateLoader(API.PLUGIN_ID, "templates/"));
		FreeMarkerTemplate.setConfiguration(config);
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
	public static BONPlugin getDefault() {
		return plugin;
	}
	
	
	/**
	 * Returns the singleton BON code scanner.
	 * 
	 * @return the singleton BON code scanner
	 */
	 public RuleBasedScanner getBONCodeScanner() {
	 	if (fCodeScanner == null)
			fCodeScanner= new BONCodeScanner(getBONColourProvider());
		return fCodeScanner;
	}
	
	/**
	 * Returns the singleton BON color provider.
	 * 
	 * @return the singleton BON color provider
	 */
	 public BONColourProvider getBONColourProvider() {
	 	if (fColorProvider == null)
			fColorProvider= new BONColourProvider();
		return fColorProvider;
	}

}
