/*
 * This file is part of the Esc/Java2 plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Aug 26, 2004
 */
package escjava.plugin;

import java.util.Iterator;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;

import pluginlib.Log;
import pluginlib.Utils;


/**
 * This is a collection of miscellaneous utility functions.
 * 
 * @author David Cok
 *
 */
public class EscjavaUtils {
	
	/** The ordered list of standard JML suffixes to search for the
	 *  most refined specification file, omitting prefixed '.'s.
	 */
	public final static String[] standardJmlSuffixes = new String[] {
			"refines-java", "refines-spec", "refines-jml", "java", "spec", "jml"
		};

	/** The standard JML suffixes, omitting 'java', with prefixed '.'s. */
    public final static String[] nonJavaSuffixes = new String[]{
    		".refines-java", ".refines-spec", ".refines-jml", ".spec", ".jml"
    };
    
	/** A convenenience holder for the IPath of the (one) workspace. */
	private static IPath workspacePath = null;
	
	/**
	 * Returns the IPath for the one workspace object.
	 * @return The IPath of the workspace.
	 */
	public static IPath workspacePath() {
		if (workspacePath == null) {
			workspacePath = Utils.getRoot().getLocation();
		}
		return workspacePath;
	}

	/** A convenience holder for the one MarkerCreator, which
	 *  manages creating and deleting JML markers.
	 */
	public final static EscjavaMarker markerCreator = new EscjavaMarker();

	
	/**
	 * Returns the absolute file-system location of the JML system specifications
	 * 
	 * @return The absolute file-system location of the JML specs
	 * @throws Exception
	 */
	static public String findSpecs() throws Exception {
		return Utils.findPluginResource("escjava.esctools","esctools2.jar");
	}
	
	/**TODO
	 * @param javaProject
	 * @param name
	 * @param location
	 */
	static public void installSpecsAsSrcFolder(IJavaProject javaProject,
			String name, String location) {
		try {
			IClasspathEntry[] classpath = javaProject.getRawClasspath();
	
			IFolder f = javaProject.getProject().getFolder(name);
			if (f.exists()) {
				Log.errorlog("Source folder " + name + " already exists in project " + javaProject.getElementName(),null);
				return;
			}
			f.createLink(new Path(location),IResource.NONE,null);
			
			IClasspathEntry[] newClasspath = new IClasspathEntry[classpath.length+1];
			System.arraycopy(classpath,0,newClasspath,0,classpath.length);
			newClasspath[classpath.length] = JavaCore.newSourceEntry(
					f.getFullPath(),
					new Path[]{new Path("**")}  // FIXME - does this exclude the folder from the classpath altogether?
					); 
			javaProject.setRawClasspath(newClasspath, null);
			// FIXME - the source folder ought to be marked as
			// exported, but there does not seem to be a way to do this
			if (Log.on) Log.log("Installed specs at " + name + " in project " + javaProject.getElementName()
					+ ", location " + location);
		} catch (Exception e) {
			Log.errorlog("Failed to install the JML specifications",e);
		}
	}

	/**
	 * If there is not already a project by the given name
	 * (the value of specsProjectName) on the classpath of 
	 * the given project, then add the project to the classpath
	 * of 'javaProject'.
	 * @param javaProject The project whose classpath is adjusted
	 * @param specsProjectName The project that is added to the classpath
	 */
	static public void installSpecsUsingProject(IJavaProject javaProject,
			String specsProjectName) {
		try {
			IClasspathEntry[] classpath = javaProject.getRawClasspath();
			for (int i=0; i<classpath.length; ++i) {
				if (classpath[i].getEntryKind() == IClasspathEntry.CPE_PROJECT) {
					IPath p = classpath[i].getPath();
					if (p.lastSegment().equals(specsProjectName)) {
						if (Log.on) Log.log("Specs library already installed " + p);
						return;
					}
				}
			}
			
			IPath specsProject = Utils.getRoot().getFullPath().append(specsProjectName);
	
			IClasspathEntry[] newClasspath = new IClasspathEntry[classpath.length+1];
			System.arraycopy(classpath,0,newClasspath,0,classpath.length);
			newClasspath[classpath.length] = JavaCore.newProjectEntry(
					specsProject);
			javaProject.setRawClasspath(newClasspath, null);
			if (Log.on) Log.log("Installed specs as project in project " + javaProject.getElementName());

		} catch (Exception e) {
			Log.errorlog("Failed to install the JML specifications as a project in " + javaProject.getElementName(),e);
		}
	}

	/**
	 * Create, if it does not already exist, a Java project with the 
	 * given name containing a source folder with the given name
	 * that links to the given location.  The source folder is
	 * entirely excluded from being built but is on the classpath.
	 * 
	 * @param projectName  The name of the Java project to create
	 * @param folderName   The name of the source folder in the project
	 * @param location	   The location (absolute file-system location path) of the specifications to link to
	 * @return  true if the project already existed, false otherwise
	 */
	static public boolean installSpecsAsProject(String projectName,
			String folderName, String location) {
		IProject project = Utils.getRoot().getProject(projectName);
		
		try {
			// Check if the project exists
			if (project.exists()) {
				if (Log.on) Log.log("Specs project already exists - " + projectName);
			} else {
				// It does not exist; create it
				project.create(null);
				project.open(null);
				// Add Java nature to it
				// (expect that it does not have any natures)
				IProjectDescription description = project.getDescription();
				String[] ids = description.getNatureIds();
				String[] newIds = new String[ids.length + 1];
				System.arraycopy(ids, 0, newIds, 0, ids.length);
				newIds[ids.length] = "org.eclipse.jdt.core.javanature";
				description.setNatureIds(newIds);
				project.setDescription(description, null);
			}

			IJavaProject javaProject = JavaCore.create(project);
			if (location.endsWith(".jar")) {
				// The location is a library 
				folderName = "jmlspecs.jar"; // Really a file, not a folder
				IFile f = project.getFile(folderName);
				f.createLink(new Path(location),IResource.NONE,null);
				// Add the library entry as the only entry to the new classpath
				// (The old classpath has the project as a classpath entry - that has
				// to be left out)
				IClasspathEntry[] newClasspath = new IClasspathEntry[1];
				newClasspath[0] = JavaCore.newLibraryEntry(
						f.getFullPath(), null, null);
				javaProject.setRawClasspath(newClasspath, null);
			} else {
				// Presume the location is a source folder
				// create the source folder by linking to the specs location
				IFolder f = project.getFolder(folderName);
				f.createLink(new Path(location),IResource.NONE,null);
								
				// Add the source entry as the only entry to the new classpath
				// (The old classpath has the project as a classpath entry - that has
				// to be left out)
				IClasspathEntry[] newClasspath = new IClasspathEntry[1];
				newClasspath[0] = JavaCore.newSourceEntry(
						f.getFullPath(), new Path[]{new Path("**")});
				javaProject.setRawClasspath(newClasspath, null);
				// FIXME - the source folder ought to be marked as
				// exported, but there does not seem to be a way to do this
			}
			
			if (Log.on) Log.log("Installed specs at " + folderName + " in project " + javaProject.getElementName()
					+ ", location " + location);
		} catch (Exception e) {
			Log.errorlog("Failed to install the JML specifications",e);
		}
		return false;
	}

	/**
	 * Checks to see whether the given project has the JML system
	 * specs on its classpath.
	 * @param javaProject The project to check
	 * @return  true if the system specs are on the classpath, 
	 * 			false otherwise
	 */
	//@ pure
	public static boolean isSpecsInstalled(IJavaProject javaProject) {
		// We do this check by taking one file that ought to be in the
		// JML specs and checking to see if it is on the classpath somewhere
		IPath pp = new Path("java/lang/Object.jml");
		Iterator i = Utils.getProjectClassPathEntries(javaProject).iterator();
		while (i.hasNext()) {
			String cpe = (String)i.next();
			IPath p = new Path(cpe);
			IResource r = Utils.getRoot().findMember(p);
			if (r instanceof IFolder) {
				if (((IContainer)r).findMember(pp) != null) return true;
			} else if (cpe.endsWith("jmlspecs.jar") ||
					   cpe.endsWith("esctools2.jar")) return true;
			// FIXME - should really check if this has 'pp' in it
			//   the above is really a hack
		}
		return false;
	}
	
	/**
	 * This method checks to see if the given Java project has 
	 * the JML specs linked into it.  If not, then a JmlSpecs
	 * project containing the JML system and model specs is 
	 * created, if it does not already exist.  Finally, the
	 * JmlSpecs project is added to the classpath of the given
	 * project.
	 * @param javaProject  The project add the JML specs to
	 */
	public static void installDefaultSpecs(IJavaProject javaProject) {
		String location = null;
		try {
			// Check to see if the specs are already linked into the project
			if (isSpecsInstalled(javaProject)) return;
			// If not, find the specs in the plugin
			location = findSpecs();
			// Create (if it does not exist) a project and link the specs into it
			installSpecsAsProject("JmlSpecs","jmlSpecs",location);
			// Put the new project on the argument project's classpath
			installSpecsUsingProject(javaProject,"JmlSpecs");
			return;
		} catch (Exception e) {
			Log.errorlog("Failed to install default specs",e);
		}	
		// Try installing as a source folder
		if (location == null) return;
		try {
			installSpecsAsSrcFolder(javaProject,"jmlSpecs",location);
		} catch (Exception e) {
			Log.errorlog("Failed to install default specs as a source folder",e);
		}
	}
	
	/**
	 * Finds the simplify executable that is part of the the plugin.
	 * @param os The name of the OS
	 * @return The location of the simplify executable as an absolute file system path.
	 * @throws Exception
	 */
	public static String findInternalSimplify(String os) throws Exception {
		if (os == null || os.length() == 0) {
			os = System.getProperty("os.name");
		}
	  String suffix = getSimplifySuffix(os);
	  if (suffix == null) return null;
	  String name = "Simplify-1.5.4." + suffix;
	  name = Utils.findPluginResource("escjava.simplify",name);
		return name;
	}
		
  public static String getSimplifySuffix(String osname) {
		String suffix = null;
		if (osname.startsWith("Windows")) suffix = "exe";
		else if (osname.equals("linux")||
		         osname.equals("Linux")) suffix = "linux";
		else if (osname.equals("darwin")||
		         osname.equals("MacOSX")||
		         osname.equals("Mac OS X")) suffix = "macosx";
		else if (osname.equals("solaris")||
		         osname.equals("Solaris")) suffix = "solaris";
		return suffix;
  }
	
}
// FIXME - check all javadoc comments

