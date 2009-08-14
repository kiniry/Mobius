package canapa;

import logs.LogType;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

import canapa.ui.console.CanapaOutputConsole;



/**
 * The main plugin class to be used in the desktop.
 */
public class CanapaPlugin extends AbstractUIPlugin {
	private static final String ID = "CANAPA plugin";
	//The shared instance.
	private static CanapaPlugin plugin;
	public static String plugin_dir;
	
	/**
	 * The constructor.
	 */
	public CanapaPlugin() {
		super();
		plugin = this;
	}
	
    public static void log(int severity, String message, Throwable e) {
		getPlugin().getLog().log(new Status(severity, ID, 0, message, e));
	}


	/**
	 * This method is called upon plug-in activation
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		setPluginDir();
		try {
		    console = new CanapaOutputConsole();
	    } catch (RuntimeException e) {
	        // Don't let the console bring down the SVN UI
	        log(IStatus.ERROR, "Errors occurred starting the CANAPA console", e);
	    }

	}

	/**
	 * This method is called when the plug-in is stopped
	 */
	public void stop(BundleContext context) throws Exception {
		super.stop(context);
	}

	private void setPluginDir(){
		//FIXME: HACK, How to get plugin dir??
		String loc = plugin.getBundle().getLocation();
		logs.Log.println(LogType.INIT, "LOC: "+loc);
		plugin_dir = loc.substring(loc.indexOf("@/")+2, loc.length());
		logs.Log.println(LogType.INIT, "DIR: "+plugin_dir);
	}
	
	public static CanapaPlugin getPlugin() {
		// If the instance has not been initialized, we will wait.
		// This can occur if multiple threads try to load the plugin at the same
		// time (see bug 33825: http://bugs.eclipse.org/bugs/show_bug.cgi?id=33825)
		while (plugin == null) {
			try {
				Thread.sleep(50);
			} catch (InterruptedException e) {
				// ignore and keep trying
			}
		}
		return plugin;
	}
	
	private CanapaOutputConsole console;

	
	public CanapaOutputConsole getConsole() {
		return console;
	}

	public static Display getStandardDisplay() {
        Display display= Display.getCurrent();
        if (display == null) {
            display= Display.getDefault();
        }
        return display; 
	}
}
