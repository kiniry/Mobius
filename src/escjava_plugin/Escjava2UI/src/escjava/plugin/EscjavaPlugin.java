/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 *
 */

package escjava.plugin;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

import pluginlib.AbstractPreference;
import pluginlib.Log;
import pluginlib.Utils;

/**
 * The main plugin class for the EscJava plugin.
 * 
 * @author David R. Cok
 */
public class EscjavaPlugin extends AbstractUIPlugin {

	public static final String ESC_TOOL_NAME = "ESC/Java2";
	/**
	 * This is the list of listeners that have registered to this plugin.
	 */
	private List listeners = new ArrayList();
	//@ constraint \not_modified(listeners);
	// The List object does not chnage, though its content might
	
	/** The shared instance of the singleton plugin. */
	private static EscjavaPlugin plugin;
	//@ initially plugin == this;
	//@ constraint \not_modified(plugin);
	
	/**
	 * The IDs of the plugins.
	 */
	public static final String UI_PLUGIN_ID = "mobius.escjava2.plugin";
	public static final String TOOLS_PLUGIN_ID = "mobius.escjava2.esctools";
	
	/**
	 * Name of jarfile of ESC/Java2 build (has been "esctools2.jar" for a *long* time).
	 */
	public static final String ESCJAVA_JAR_FILENAME = "esctools2.jar";
	
	/**
   * Name of jarfile of JML specs file (has been "jmlspecs.jar" for a *long* time).
   */
  public static final String JML_JAR_FILENAME = "jmlspecs.jar";
  
  /**
   * The name of the automatically-generated project that contains our specfications.
   */
  public static final String JMLSPECS_PROJECT_NAME = "jmlspecs";
  
	/**
	 * This is the id of the auto-check nature extension made for Escjava checking
	 */
	public static final String ESCJAVA_AUTOCHECK_NATURE = UI_PLUGIN_ID + ".autocheckEscjavaNature";
	
	/**
	 * This is the id of the auto-check builder extension made for Escjava checking
	 */
	public static final String ESCJAVA_AUTOCHECK_BUILDER = UI_PLUGIN_ID + ".autocheckEscjavaBuilder";
	

	/**
	 * The constructor.
	 */
	//@ ensures plugin == this;
	//@ pure
	public EscjavaPlugin() {
		super();
		plugin = this;
	}

	/**
	 * This method is called upon plug-in activation
	 * @param context
	 * @throws Exception
	 */
	//@ modifies Log.log, Log.log.content
	public void start(BundleContext context) throws Exception {
		super.start(context);
		Log.createLog(EscjavaPlugin.ESC_TOOL_NAME,this);
    AbstractPreference.preferenceStore = getPlugin().getPreferenceStore();
		AbstractPreference.addListener(
				new AbstractPreference.Listener() {
					public void run() {
						Log.initializeState(
								Options.logging.getValue(),
								Options.useConsole.getValue(),
								Options.alsoLogInfo.getValue());
					}
				});
		AbstractPreference.notifyListeners();
		if (Log.on) Log.log(ESC_TOOL_NAME + " plugin is starting");

		// FIXME this does not work
		// Add the file associations
//		IEditorRegistry registry = PlatformUI.getWorkbench().getEditorRegistry();
//		String s = registry.getDefaultEditor("*.java").getId();
//		String[] suffixes = EscjavaUtils.nonJavaSuffixes;
//		for (int k = 0; k < suffixes.length; ++k) registry.setDefaultEditor("*" + suffixes[k],s);
//		if (Log.on) Log.log("Added file associations");
		
		// There is just one, permanent, listener
		addEscjavaListener(EscjavaUtils.markerCreator);
	}

	/**
	 * This method is called when the plug-in is stopped
	 * @param context
	 * @throws Exception
	 */
	//@ modifies Log.log.content;
	public void stop(BundleContext context) throws Exception {
		removeEscjavaListener(escjava.plugin.EscjavaUtils.markerCreator);
		if (Log.on) Log.log(ESC_TOOL_NAME + " plugin is stopping");
		super.stop(context);
	}

	/**
	 * Returns the shared instance.
	 * @return the shared instance
	 */
	//@ ensures \result == plugin;
	//@ pure
	public static EscjavaPlugin getPlugin() {
		return plugin;
	}

	/**
	 * This method adds the auto-check nature to the argument project. This is done
	 * so that we can have the Escjava checker builder running.
	 * 
	 * @param project The project for which the nature will be set
	 * @throws CoreException
	 */
	public void addEscjavaAutocheckNature(IProject project) throws CoreException {
		boolean b = Utils.addNature(project,ESCJAVA_AUTOCHECK_NATURE);

		if (Log.on) {
			if (!b) Log.log(ESC_TOOL_NAME + " Nature is already present - " + project.getName());
			else    Log.log(ESC_TOOL_NAME + " Nature added - " + project.getName());
		}
	}
	
	/**
	 * This removes the auto-check nature from the argument project. This is done
	 * so that we can have the Escjava checker stop running.
	 * 
	 * @param project The project from which the Escjava autocheck nature will be removed
	 * @throws CoreException
	 */
	public void removeEscjavaAutocheckNature(IProject project) throws CoreException {
		
		// Just traverse the list of all natures for this project. If the auto JML check nature
		// is found, remove it.
		
		boolean b = Utils.removeNature(project,ESCJAVA_AUTOCHECK_NATURE);
		if (Log.on) {
			if (!b) Log.log(ESC_TOOL_NAME + " Nature is not present - " + project.getName());
			else    Log.log(ESC_TOOL_NAME + " Nature was removed - " + project.getName());
		}
	}

	/**
	 * Remove a given listener from the list of registered listeners to this plugin.
	 * 
	 * @param listener The listener to be removed
	 */
	private void removeEscjavaListener(IEscjavaListener listener) {
		listeners.remove(listener);
	}

	/**
	 * Register a listener to this plugin.
	 * 
	 * @param listener The listener to be registered
	 */
	private void addEscjavaListener(IEscjavaListener listener) {
		listeners.add(listener);
	}
	
	/**
	 * This method informs the registered listeners that the event 'JML type checking failed' just
	 * happened and provides them with descriptive information about the event.
	 *
	 * @param resource The resource to associate with the failure, if the file is not a resource
	 * @param file The file where the event took place
	 * @param lineNumber The 1-based line number where the event took place
	 * @param offset The 0-based character offset within the file that begins the error location
	 * @param length The length in characters of the error location
	 * @param errorMessage A message describing the event
	 * @param severity The severity of the event (uses severity constants from IEscjavaListener)
	 * @throws Exception
	 */
	public void fireEscjavaFailed(final IResource resource, 
			final String file,
			final int lineNumber, final int offset, final int length,
			final String errorMessage, final int severity) throws Exception {
		for (Iterator all = listeners.iterator(); all.hasNext(); ) {
			final IEscjavaListener each = (IEscjavaListener) all.next();
			each.escjavaFailed(resource, file, lineNumber, offset, length, errorMessage, severity);
		}
	}
}
