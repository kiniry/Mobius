/*
 * This file is part of a library of utilities for plugin projects.
 * Copyright 2004 David R. Cok
 * 
 * Created on Oct 6, 2004
 */
package pluginlib;

import java.io.BufferedInputStream;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.nio.ByteBuffer;
import java.nio.charset.Charset;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.osgi.framework.Bundle;

/**
 * This class contains a number of (static) utility methods for
 * use in plugins.
 * 
 * @author David R. Cok
 */
public class Utils {

	/** A convenience holder for the end-of-line String for the current platform. */
	final static public String eol = System.getProperty("line.separator"); // FIXME - is this right?

	/**
	 * @return The singleton IWorkspaceRoot for the workspace
	 */
	public static IWorkspaceRoot getRoot() {
		return ResourcesPlugin.getWorkspace().getRoot();
	}
	
	/**
	 * Adds the given nature to the given project, if it is not already added
	 * @param project The project to add the nature to
	 * @param natureId The nature to add
	 * @return true if the nature is added, false if the nature was already present
	 * @throws CoreException
	 */
	public static boolean addNature(IProject project, String natureId) throws CoreException {

		// if the project already has the nature, we return
		if(project.hasNature(natureId)) {
			return false;
		}
			
		// First we get the description object and then add the new nature ID to the project's 
		// description
		
		IProjectDescription description = project.getDescription();
		String[] ids = description.getNatureIds();
		String[] newIds = new String[ids.length + 1];
		System.arraycopy(ids, 0, newIds, 0, ids.length);
		newIds[ids.length] = natureId;
		description.setNatureIds(newIds);
		project.setDescription(description, null);
		return true;
	}

	/**
	 * Removes the given nature from the given project, if it is present
	 * @param project The project to remove the nature from
	 * @param natureId The nature to remove
	 * @return true if the nature was removed, false if the nature was not present
	 * @throws CoreException
	 */
	public static boolean removeNature(IProject project, String natureId) throws CoreException {
		IProjectDescription description = project.getDescription();
		String[] ids = description.getNatureIds();
		
		for(int i = 0; i < ids.length; ++i) {
			if(ids[i].equals(natureId)) {
				String[] newIds = new String[ids.length - 1];
				System.arraycopy(ids, 0, newIds, 0, i);
				System.arraycopy(ids, i + 1, newIds, i, ids.length - i - 1);
				description.setNatureIds(newIds);
				project.setDescription(description, null);
				return true;
			}
		}
		return false;
	}

	/* NOTE:
	 * Builders can be present in a project in either an enabled or
	 * disabled state.  I cannot find any API to switch between the
	 * two - in the UI, there is a toggle on the Builders page of the
	 * project preferences.  Consequently we muck with what I would
	 * presume is an internal representation in isDisabledCommand
	 * and newDisabledCommand.  The representation may well change;
	 * it also may not be robust for commands that have arguments.
	 * 
	 * I implemented these commands for four reasons: (a) to be able
	 * to add builders in the disabled state,  (b) to be able to
	 * provide menu and accelerator key mechanisms for a user to 
	 * turn builders on and off, (c) to be able to determine
	 * whether a builder was enabled or not, to give some feedback
	 * to the user, and (d) to avoid some bad behavior of disabled
	 * builders not being removed when a nature was removed.
	 * 
	 */
	/** This is the builder name used for disabled commands. */
	private static final String disabledBuilderName = "org.eclipse.ui.externaltools.ExternalToolBuilder";

	/** This is the attribute key used for disabled commands. */
	private static final String disabledBuilderKey = "LaunchConfigHandle";

	/**
	 * This routine checks whether the given command is an
	 * enabled instance of the given builder.
	 *  
	 * @param c The command to be tested
	 * @param b The builder
	 * @return true if the command is a enabled instance of the builder, false otherwise
	 */
	public static boolean isEnabledCommand(ICommand c, String b) {
		return c.getBuilderName().equals(b);
	}

	/**
	 * This routine checks whether the given command is a
	 * disabled instance of the given builder.  This may well
	 * be fragile with version changes.
	 * @param c The command to be tested
	 * @param b The builder
	 * @return true if the command is a disabled instance of the builder, false otherwise
	 */
	public static boolean isDisabledCommand(ICommand c, String b) {
		if (!c.getBuilderName().equals(disabledBuilderName)) return false;
		Map m = c.getArguments();
		Object v = m.get(disabledBuilderKey);
		if (v != null && (v instanceof String) &&
				((String)v).indexOf(b) != -1) return true;
		return false;
	}
	
	/**
	 * This method creates a new builder command of the specified type, but in
	 * a disabled state.  It is not valid if there already is a builder of this
	 * type present.
	 * 
	 * @param project 	   The project to which this will belong
	 * @param description  The project description
	 * @param builder      The builder name
	 * @return				the new builder command
	 * @throws CoreException
	 */
	public static ICommand newDisabledCommand(final IProject project, final IProjectDescription description, final String builder) throws CoreException {
		// Put this in a resource change environment
		final ICommand command = description.newCommand();
		ResourcesPlugin.getWorkspace().run(
				new IWorkspaceRunnable() {
					public void run(IProgressMonitor pm) throws CoreException {
						command.setBuilderName(disabledBuilderName);
						Map map = new HashMap();
						map.put(disabledBuilderKey,"<project>/.externalToolBuilders/"+builder+".launch");
						command.setArguments(map);
						IFolder dir = project.getFolder(".externalToolBuilders");
						if (!dir.exists()) dir.create(true,true,null);
						IFile f = dir.getFile(builder + ".launch");
						if (f.exists()) f.delete(true,false,null);
						String content = 
							"<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol +
							"<launchConfiguration type=\"org.eclipse.ant.AntBuilderLaunchConfigurationType\">" + eol +
							"<booleanAttribute key=\"org.eclipse.ui.externaltools.ATTR_BUILDER_ENABLED\" value=\"false\"/>" + eol +
							"<mapAttribute key=\"org.eclipse.ui.externaltools.ATTR_TOOL_ARGUMENTS\"/>" + eol +
							"<stringAttribute key=\"org.eclipse.ui.externaltools.ATTR_DISABLED_BUILDER\" value=\"" + builder + "\"/>" + eol +
							"</launchConfiguration>";
						ByteBuffer bb = Charset.forName("UTF-8").encode(content);
						f.create(new ByteArrayInputStream(bb.array(),bb.position(),bb.limit()-bb.position()),true,null);
					}
				}, null); // no progress monitor

		return command;
	}


	/**
	 * Adds the given builder to the list of commands.
	 * @param project   The project whose commands are being added to
	 * @param commands  The current set of project commands
	 * @param description The current project's description
	 * @param builder   The name of the builder to add, if not already present.
	 * @param enabled   If true, the builder is installed in the enabled state, if false
	 * 					it is installed in the disabled state
	 * @return			The resulting set of commands.
	 * @throws CoreException
	 */
	public static ICommand[] addBuilder(IProject project, ICommand[] commands, 
			IProjectDescription description, String builder, boolean enabled) throws CoreException {
		// If the builder is already specified as one of the build actions, do nothing
		
		for(int i = 0; i < commands.length; ++i) {
			ICommand c = commands[i];
			boolean isEnabled = isEnabledCommand(c,builder);
			if (isEnabled || isDisabledCommand(c,builder)) {
				if (Log.on) Log.log("Builder " + builder + " already added to " + project.getName() + " : " +
						(isEnabled ? "enabled" : "disabled"));
				return commands;
			}
		}
		
		// Otherwise, put the builder among the project's build actions
		
		ICommand command;
		if (enabled) {
			command = description.newCommand();
			command.setBuilderName(builder);
		} else {
			command = newDisabledCommand(project,description,builder);
		}
		ICommand[] newCommands = new ICommand[commands.length + 1];
		System.arraycopy(commands, 0, newCommands, 0, commands.length);
		newCommands[newCommands.length - 1] = command;
		if (Log.on) Log.log("Builder " + builder + " added to " 
				+ project.getName() +
				(enabled?" enabled":" disabled"));
		return newCommands;
	}

	/**
	 * Adds an enabled builder to the given project
	 * @param project The project to add a builder to
	 * @param builder The builder to add
	 * @throws CoreException
	 */
	public static void addBuilder(IProject project, String builder) throws CoreException {
		IProjectDescription description = project.getDescription();
		ICommand[] commands = description.getBuildSpec();
		commands = addBuilder(project,commands,description,
				builder,
				true);
		description.setBuildSpec(commands);
		project.setDescription(description, null);
	}
	
	/**
	 * Removes the given builder from the list of commands.
	 * @param commands  The current set of project commands
	 * @param builder   The name of the builder to remove, if present.
	 * @return			The resulting set of commands.
	 */
	public static ICommand[] removeBuilder(ICommand[] commands, String builder) {
		// If any of the commands is the builder, remove it and return
		for (int i = 0; i < commands.length; ++i) {
			ICommand c = commands[i];
			boolean isEnabled = isEnabledCommand(c,builder);
			if (isEnabled || isDisabledCommand(c,builder)) {
				ICommand[] newCommands = new ICommand[commands.length - 1];
				System.arraycopy(commands, 0, newCommands, 0, i);
				System.arraycopy(commands, i + 1, newCommands, i, commands.length - i - 1);
				return newCommands;
			}
		}
		return commands;
	}

	/**
	 * Removes the given builder from a project.
	 * @param project   The project whose builder is to be removed
	 * @param builder   The name of the builder to remove, if present.
	 * @throws CoreException
	 */
	public static void removeBuilder(IProject project, String builder) throws CoreException {
		IProjectDescription description = project.getDescription();
		ICommand[] commands = description.getBuildSpec();
		commands = removeBuilder(commands,builder);
		description.setBuildSpec(commands);
		project.setDescription(description, null);
	}
	
//	/**
//	 * If the builder is not present in the commands list, no action occurs;
//	 * if it is present and disabled, it is enabled;
//	 * if it is present and enabled, no action occurs.
//	 * 
//	 * @param commands  The current set of project commands
//	 * @param description The description of the project
//	 * @param builder   The name of the builder to enable.
//	 * @return			The resulting set of commands.
//	 */
//	public ICommand[] enableBuilder(ICommand[] commands, 
//			IProjectDescription description, String builder) {
//		
//		for (int i = 0; i < commands.length; ++i) {
//			ICommand c = commands[i];
//			if (isEnabledCommand(c,builder)) return commands;
//			if (isDisabledCommand(c,builder)) {
//				ICommand command = description.newCommand();
//				command.setBuilderName(builder);
//				commands[i] = command;
//				return commands;
//			}
//		}
//		return commands;
//	}
//
//
//	/**
//	 * If the builder is not present in the commands list, no action occurs;
//	 * if it is present and disabled, no action occurs;
//	 * if it is present and enabled, it is disabled.
//	 * 
//	 * @param project   The project whose builder is being disabled
//	 * @param commands  The current set of project commands
//	 * @param description The description of the project
//	 * @param builder   The name of the builder to enable.
//	 * @return			The resulting set of commands.
//	 * @throws CoreException
//	 */
//	public static ICommand[] disableBuilder(IProject project, ICommand[] commands, 
//			IProjectDescription description, String builder) throws CoreException  {
//		
//		for (int i = 0; i < commands.length; ++i) {
//			ICommand c = commands[i];
//			if (isEnabledCommand(c,builder)) {
//				commands[i] = newDisabledCommand(project, description,builder);
//				return commands;
//			}
//			if (isDisabledCommand(c,builder)) return commands;
//		}
//		return commands;
//	}

	/**
	 * Checks whether a project is enabled for a given builder
	 * (both has the builder and the builder is turned on).
	 * @param p  The project to check
	 * @param builder The id of the builder to look for
	 * @return true if the project has the builder and it is enabled,
	 * 			false otherwise
	 * @throws CoreException
	 */
	public static boolean isBuilderEnabled(IProject p, String builder) throws CoreException {
		
		ICommand[] commands = p.getDescription().getBuildSpec();
		for (int i = 0; i < commands.length; ++i) {
			ICommand c = commands[i];
			if (isEnabledCommand(c,builder)) return true;
		}
		return false;
	}

	
	/**
	 * A convenience method for getting all of the Java projects in the 
	 * workspace.
	 * @return An array of the IJavaProject objects in the workspace
	 */
	public static IJavaProject[] getJavaProjects() {
		IProject[] projects = getRoot().getProjects();
		Collection list = new LinkedList();
		for (int i=0; i<projects.length; ++i) {
			IJavaProject jp = JavaCore.create(projects[i]);
			if (jp != null) list.add(jp);
		}
		return (IJavaProject[]) list.toArray(new IJavaProject[list.size()]);
	}

	
	/**
	 * Computes the classpath (in terms of full absolute file-system paths to
	 * directories) from the information available in the Eclipse project.
	 * Note that this involves recursively processing the classpath contributions
	 * from projects that are on the Eclipse classpath for the requested project.
	 *
	 * @param project The project whose classpath is to be determined.
	 * @return The classpath of the argument in full absolute file-system paths,
	 * 		separated by the platform's path separator
	 */
	// FIXME - may need to distinguish source and binary classpaths?
	static public String getProjectClassPath(IJavaProject project) {

		StringBuffer classPath = new StringBuffer(System.getProperty("java.class.path"));
		List list = new LinkedList();
		
		addResolvedClassPathEntries(list,project,false);

		Iterator i = list.iterator();
		while (i.hasNext()) {
			classPath.append(java.io.File.pathSeparator);
			classPath.append(i.next());
		}
		return classPath.toString();
	}
	
	/**
	 * Gets the classpath entries for the given project and adds
	 * them to the List as file-system absolute paths (String);
	 * required projects are added recursively; libraries are added
	 * once; source folders are converted to file system absolute
	 * paths (remember that source folders may be linked).
	 * 
	 * @param project
	 * @return List of String containing classpath locations
	 */
	static public List getProjectClassPathEntries(IJavaProject project) {
		//StringBuffer classPath = new StringBuffer(System.getProperty("java.class.path"));
		List list = new LinkedList();		
		addResolvedClassPathEntries(list,project,false);
		return list;
		// FIXME - does not include the system entries
	}

	/** TODO
	 * @param list
	 * @param project
	 * @param onlyExported
	 */
	// FIXME - Ought to use the information that a classpathentry is exported, but the
	// value of cpe.isExported() does not seem to reflect the setting in the Java BuildPath properties.
	// Thus here we arbitrarily state that only source entries are exported, not
	// libraries or projects.
	static void addResolvedClassPathEntries(List list, IJavaProject project, boolean onlyExported) {
		try {
			IClasspathEntry[] classPathEntries = project.getResolvedClasspath(false);
			
			for (int i = 0; i < classPathEntries.length; ++i) {
				IClasspathEntry cpe = classPathEntries[i];
				IPath entry = cpe.getPath();
				if (onlyExported && 
						(cpe.getEntryKind() != IClasspathEntry.CPE_SOURCE &&
								!entry.toOSString().endsWith(escjava.plugin.EscjavaPlugin.JML_JAR_FILENAME) )) continue; // FIXME no explicit library names
				IResource res = getRoot().findMember(entry);
				if (cpe.getEntryKind() == IClasspathEntry.CPE_LIBRARY) {
					// Might be an internal or external library
					if (res != null) {
						// internal
						list.add(res.getRawLocation().toOSString());
						// NOTE: Per the note below, it is not entirely clear
						// whether the above should be getLocation or getRawLocation
						// FIXME - try a linked library, if that is possible
					} else {
						// external
						list.add(entry.toOSString());
					}
				} else if (cpe.getEntryKind() == IClasspathEntry.CPE_SOURCE) {
					// The Eclipse documentation is a bit unclear or at odds with
					// the actual behavior.  What I observe is that
					// - a linked folder gives the same result for getLocation and getRawLocation
					// - a project that is also a source folder gives null for getRawLocation
					// Thus experiment would indicate that getLocation could always be used,
					// but the documentation implies one could always use getRawLocation.  The following
					// code is trying to be conservative. (NOTE)
					if (res.isLinked()) list.add(res.getRawLocation().toOSString());
					else list.add(res.getLocation().toOSString());
				} else if (cpe.getEntryKind() == IClasspathEntry.CPE_PROJECT) {
					IJavaProject jp = JavaCore.create((IProject)res);
					if (jp != null) addResolvedClassPathEntries(list,jp,true);
					else {
						// FIXME - throw an error of some sort
					}
				} else {
					Log.errorlog("Unexpected content kind as a classpath entry: " + cpe.getEntryKind(),null);
				}
			}
		} catch (JavaModelException e) {
			Log.errorlog("Unexpected failure to process the classpath or project does not have a Java nature: ",e);
		}		
	}
	
	/**
	 * Converts a location (file system absolute path) into an IResource within
	 * the given project by searching the classpath for a source folder that
	 * contains the given location.  The problem is that source folders or files
	 * may be linked and consequently a location's absolute path does not tell
	 * what IResource it might be. 
	 * 
	 * @param project  The Java Project to look for a resource in
	 * @param location The absolute file system location to map into a resource
	 * @param onlyExported  FIXME
	 * @return  FIXME
	 */
	public static IResource mapBack(IJavaProject project, String location, boolean onlyExported) {
		try {
			IClasspathEntry[] classPathEntries = project.getResolvedClasspath(false);
			
			for (int i = 0; i < classPathEntries.length; ++i) {
				IClasspathEntry cpe = classPathEntries[i];
				if (onlyExported && cpe.getEntryKind() != IClasspathEntry.CPE_SOURCE) continue;
				IPath entry = cpe.getPath();
				IResource res = getRoot().findMember(entry);
				if (cpe.getEntryKind() == IClasspathEntry.CPE_LIBRARY) {
					// Might be an internal or external library
					// skip
				} else if (cpe.getEntryKind() == IClasspathEntry.CPE_SOURCE) {
					// The Eclipse documentation is a bit unclear or at odds with
					// the actual behavior.  What I observe is that
					// - FIXME what about a non-linked folder
					// - a linked folder gives the same result for getLocation and getRawLocation
					// - a project that is also a source folder gives null for getRawLocation
					// Thus experiment would indicate that getLocation could always be used,
					// but the documentation implies one could always use getRawLocation.  The following
					// code is trying to be conservative. (NOTE)
					if (res.isLinked()) {
						String s = res.getRawLocation().toOSString();
						if (location.startsWith(s)) {
							IPath p = res.getFullPath().append(location.substring(s.length()));
							IResource r = getRoot().findMember(p);
							if (r != null) return r;
						}
					} // FIXME - what about non-linked?
				} else if (cpe.getEntryKind() == IClasspathEntry.CPE_PROJECT) {
					IResource s = mapBack(JavaCore.create((IProject)res),location,true);
					if (s != null) return s;
				} else {
					Log.errorlog("Unexpected content kind as a classpath entry: " + cpe.getEntryKind(),null);
				}
			}
		} catch (JavaModelException e) {
			Log.errorlog("Unexpected failure to process the classpath or project does not have a Java nature: ",e);
		}
		return null;
	}

	/**
	 * Displays a message in a dialog in the UI thread - this may
	 * be called from other threads.
	 * @param sh  The shell to use to display the dialog, or 
	 * 		a top-level shell if the parameter is null
	 * @param title  The title of the dialog window
	 * @param msg  The message to display in the dialog
	 */
	//@ requires title != null;
	//@ requires msg != null;
	static public void showMessageInUI(Shell sh, final String title, final String msg) {
		final Shell shell = sh;
		Display d = shell == null ? Display.getDefault() : shell.getDisplay();
		d.asyncExec(new Runnable() {
				public void run() {
					MessageDialog.openInformation(
							shell,
							title,
							msg);
				}
			});
	}

	/**
	 * Displays a message in a information dialog; must be called from the UI thread.
	 * @param shell  Either the parent shell, or null for a top-level shell
	 * @param title  A title for the dialog window
	 * @param msg   The message to display in the dialog window
	 */
	//@ requires shell != null;
	//@ requires title != null;
	//@ requires msg != null;
	static public void showMessage(Shell shell, String title, String msg) {
			MessageDialog.openInformation(
				shell,
				title,
				msg);
	}

	
	/**
	 * Returns the absolute file system location of a file inside a plugin.
	 * @param pluginName  The name of the plugin
	 * @param path  The path (as a String) of the file within the plugin
	 * @return The absolute file system location of the target file
	 * @throws IOException
	 */
	public static String findPluginResource(String pluginName, String path) throws IOException {
		// This is the 'official' way to find something that
		// is in the install location of the plugin, cf.
		// Official Eclipse Faq #103.
		// It is stated that this code will only work if the 
		// install location is on the local file system.
		Bundle bundle = Platform.getBundle(pluginName);
		
		IPath p = new Path(path);
		URL url = FileLocator.find(bundle, p, null);
		// The substring call is to remove an initial /
		// FIXME do we remove the / on all platforms?
		// FIXME - do we need to do these back-and-forth conversions of wil this do:
		// return Platform.resolve(url).getPath().substring(1);
		URL resolvedURL = FileLocator.resolve(url);
		String filePath = resolvedURL.getPath();
		Path resourcePath = new Path(filePath);
		p = resourcePath.makeAbsolute();
		String s = p.toOSString();
		if (System.getProperty("os.name").startsWith("Windows")) s = s.substring(1);
		return s;
	}
	
	/**
	 * This method does what I think s.replaceAll("\\","\\\\")
	 * is supposed to do, but that crashes.
	 * @param s Input string
	 * @return the input string with any occurrence of a backslash
	 *    replaced by a double backslash
	 */
	public static String doubleBackslash(String s) {
		StringBuffer b = new StringBuffer();
		int n = s.length();
		int i = 0;
		int j = 0;
		while (i < n) {
			if (s.charAt(i) == '\\') {
				b.append(s.substring(j,i));
				b.append("\\\\");
				++i;
				j = i;
			} else {
				++i;
			}
		}
		b.append(s.substring(j,i));
		return b.toString();
	}

	
	/**
	 * This method interprets the selection returning a List
	 * of IJavaElement and IResource objects that the plugin
	 * knows how to handle.
	 * 
	 * @param selection  The selection to inspect
	 * @param window  The window in which a selected editor exists
	 * @return A List of IJavaElement and IResource
	 */
	public static List getSelectedElements(ISelection selection, IWorkbenchWindow window ) {
		List list = new LinkedList();
		if (!selection.isEmpty()) {
			if (selection instanceof IStructuredSelection) {
				IStructuredSelection structuredSelection = (IStructuredSelection) selection;
				for (Iterator iter = structuredSelection.iterator(); iter.hasNext(); ) {
					Object element = iter.next();
					if (element instanceof IJavaElement) {
						list.add(element);
					} else if (element instanceof IResource) {
						list.add(element);
					}
				}
			} else if (selection instanceof ITextSelection){
				IEditorPart editor = window.getActivePage().getActiveEditor();
				IResource resource = (IResource) editor.getEditorInput().getAdapter(IFile.class);
				IJavaElement element = JavaCore.create(resource);
				if (element != null)
					list.add(element);
				else
					list.add(resource);
			}
		}
		return list;
	}

	/**
	 * Creates a map indexed by IJavaProject, with the value for
	 * each IJavaProject being a Collection consisting of the subset
	 * of the argument that belongs to the Java project.
	 * 
	 * @param elements The set of elements to sort
	 * @return The resulting Map of IJavaProject to Collection
	 */
	/*@ requires elements != null;
	    requires elements.elementType <: IResource ||
	             elements.elementType <: IJavaElement;
	    ensures \result != null;
	 */
	public static Map sortByProject(Collection elements) {
		Map map = new HashMap();
		Iterator i = elements.iterator();
		while (i.hasNext()) {
			Object o = i.next();
			IJavaProject jp;
			if (o instanceof IResource) {
				jp = JavaCore.create(((IResource)o).getProject());
			} else if (o instanceof IJavaElement) {
				jp = ((IJavaElement)o).getJavaProject();
			} else {
				Log.errorlog("INTERNAL ERROR: Unexpected content for a selection List - " + o.getClass(),null);
				continue;
			}
			addToMap(map,jp,o);
		}
		return map;
	}

	/**
	 * Creates a map indexed by IPackageFragmentRoot, with the value for
	 * each IPackageFragmentRoot being a Collection consisting of the subset
	 * of the argument that belongs to the IPackageFragmentRoot.
	 * 
	 * @param elements The set of elements to sort
	 * @return The resulting Map of IJavaProject to Collection
	 * @throws CoreException
	 */
	/*@ requires elements != null;
	    requires elements.elementType <: IResource ||
	             elements.elementType <: IJavaElement;
	    ensures \result != null;
	 */
	public static Map sortByPackageFragmentRoot(Collection elements) throws CoreException {
		Map map = new HashMap();
		Iterator i = elements.iterator();
		while (i.hasNext()) {
			Object o = i.next();
			IPackageFragmentRoot pfr = null;
			if (o instanceof IResource) {
				IJavaElement oo = JavaCore.create((IResource)o);
				if (oo != null) o = oo;
				else if (o instanceof IFile) {
					// Could be a specification file
					// Find the package fragment root it is in
					IFile f = (IFile)o;
					IJavaProject p = JavaCore.create(f.getProject());
					if (p == null) continue; // everything should be in a Java Project // FIXME - log an error
					IPackageFragmentRoot[] roots = p.getPackageFragmentRoots();
					IPath path = f.getFullPath();
					for (int k=0; k<roots.length; ++k) {
						IPackageFragmentRoot root = roots[k];
						IFolder rootFolder = (IFolder)root.getCorrespondingResource();
						// Is f in (or equal to) rootFolder?
						if (rootFolder.getFullPath().isPrefixOf(path)) {
							// rootFolder contains f
							pfr = root; // This is the one root that contains f
							break;
							// added to map at end of method
						} 
					}
					if (pfr == null) {
						// FIXME - improve this error message
						Log.errorlog("FILE is not in a root folder: " + path,null);
						for (int k=0; k<roots.length; ++k) {
							IPackageFragmentRoot root = roots[k];
							Log.errorlog("  ROOT " + root.getResource().getFullPath(),null);
						}
						continue; // FIXME - file is not in a root folder
					}
					
				} else if (o instanceof IFolder) {
					// Could be a folder within a project, such as a source folder or a folder
					// that holds only specification files (which won't be recognized as a package)
					// Want any roots within that folder
					// FIXME - review and test this
					IFolder f = (IFolder)o;
					IJavaProject p = JavaCore.create(f.getProject());
					if (p == null) continue; // everything should be in a Java Project // FIXME - log an error
					IPackageFragmentRoot[] roots = p.getPackageFragmentRoots();
					for (int k=0; k<roots.length; ++k) {
						IPackageFragmentRoot root = roots[k];
						if (root.isArchive()) continue;
						IFolder rootFolder = (IFolder)root.getCorrespondingResource();
						// Is f in (or equal to) rootFolder?
						if (rootFolder.getFullPath().isPrefixOf(f.getFullPath())) {
							// rootFolder contains f
							pfr = root; // This is the one root that contains f
							// added to map at end of method
						} else if (f.getFullPath().isPrefixOf(rootFolder.getFullPath())) {
							// f contains rootFolder
							addToMap(map,root,root);
						}
					}
					if (pfr == null) continue;
				}
			} else if (o instanceof IJavaProject) {
				// separate out and include all the roots within the project
				IPackageFragmentRoot[] roots = ((IJavaProject)o).getPackageFragmentRoots();
				for (int j = 0; j<roots.length; j++) {
					pfr = roots[j];
					if (!pfr.isArchive()) addToMap(map,pfr,pfr);
				}
				continue;
			} else if (o instanceof IJavaElement) {
				if (o instanceof IPackageFragmentRoot) {
					pfr = (IPackageFragmentRoot)o;
				} else if (o instanceof IPackageFragment) {
					pfr = (IPackageFragmentRoot)((IPackageFragment)o).getParent();
				} else if (o instanceof ICompilationUnit) {
					pfr = (IPackageFragmentRoot)((ICompilationUnit)o).getParent().getParent();
				} else {
					continue; // Log an internal error ??? FIXME
				}
			} else {
				continue; // log an internal error ??? FIXME
			}
			if (pfr.isArchive()) continue;
			addToMap(map,pfr,o);
		}
		return map;
	}

	/**
	 * If key is not a key in the map, it is added, with an empty
	 * Collection for its value; then the given object is added
	 * to the Collection for that key.
	 * @param map A map of key values to Collections
	 * @param key A key value to add to the map, if it is not
	 * 		already present
	 * @param object An item to add to the Collection for the given key
	 */
	private static void addToMap(Map map, Object key, Object object) {
		Collection list = (Collection)map.get(key);
		if (list == null) map.put(key, list = new LinkedList());
		list.add(object);
	}

	/**
	 * Reads input from the input and writes it to the output until
	 * the input stream runs out of data, but does all this in a new thread.
	 * @param i Stream to read from
	 * @param o Stream to write to
	 */
	public static void readAllInput(final InputStream i, final OutputStream o) {
		(new Thread(){
			public void run() {
				try {
					int n;
					byte[] b = new byte[1000];
					while ((n=i.read(b)) != -1) {
						o.write(b,0,n);
					}
					o.flush();
					return;
				} catch (Exception e) {
					// FIXME - do something here???
					return;
				}
			}
		}).start();
	}

	/**TODO
	 * @param args
	 * @return
	 * @throws IOException
	 * @throws InterruptedException
	 */
	public static int execAndWait(String[] args) throws IOException, InterruptedException {
		Process p = Runtime.getRuntime().exec(args);
		Utils.readAllInput(new BufferedInputStream(p.getInputStream()),Log.logPrintStream());
		Utils.readAllInput(new BufferedInputStream(p.getErrorStream()),Log.logPrintStream());									
		int z = p.waitFor();
		return z;
	}
	
	/**TODO
	 * @param command
	 * @param env
	 * @param cd
	 * @return
	 * @throws IOException
	 * @throws InterruptedException
	 */
	public static int execAndWait(String command, String[] env, File cd) throws IOException, InterruptedException {
		Process p = Runtime.getRuntime().exec(command,env,cd);
		Utils.readAllInput(new BufferedInputStream(p.getInputStream()),Log.logPrintStream());
		Utils.readAllInput(new BufferedInputStream(p.getErrorStream()),Log.logPrintStream());									
		int z = p.waitFor();
		return z;
	}
}
