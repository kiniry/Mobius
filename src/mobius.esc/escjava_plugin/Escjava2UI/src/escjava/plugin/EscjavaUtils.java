/*
 * This file is part of the Esc/Java2 plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Aug 26, 2004
 */
package escjava.plugin;

import java.io.IOException;

import mobius.escjava2.EscToolsActivator;
import mobius.escjava2.EscToolsActivator.JavaVersions;
import mobius.util.plugin.Log;
import mobius.util.plugin.Utils;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;



/**
 * This is a collection of miscellaneous utility functions.
 * 
 * @author David Cok
 *
 */
public final class EscjavaUtils {

  
  
  /** The ordered list of standard JML suffixes to search for the
   *  most refined specification file, omitting prefixed '.'s.
   */
  public static final String[] standardJmlSuffixes = new String[] {
    "refines-java", "refines-spec", "refines-jml", "java", "spec", "jml"
  };

  /** The standard JML suffixes, omitting 'java', with prefixed '.'s. */
  public static final String[] nonJavaSuffixes = new String[]{
    ".refines-java", ".refines-spec", ".refines-jml", ".spec", ".jml"
  };
    
  /** A convenience holder for the one MarkerCreator, which
   *  manages creating and deleting JML markers.
   */
  public static final EscjavaMarker markerCreator = new EscjavaMarker();
  
  /** A convenience holder for the IPath of the (one) workspace. */
  private static IPath workspacePath;

  /** */
  private EscjavaUtils() { }
  

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


  
  /**
   * Returns the absolute file-system location of the JML specifications for 
   * whichever version of Java is being checked.
   * 
   * @return The absolute file-system location of the JML specifications for
   *         whichever version of Java is being checked
   * @throws Exception
   */
  public static /*@ non_null @*/ String findSpecs() {
    String  specLocation = null;
    
    final JavaVersions jv = JavaVersions.selected(Options.source.getStringValue());
    specLocation = jv.getSpecsJarfileName();

    
    // Locate the specification
    String pluginResource = null;
    try {
      pluginResource = Utils.findPluginResource(
            EscToolsActivator.PLUGIN_ID, specLocation);
    }
    
    // Log useful information if specification cannot be found
    catch (IOException ex) {
      Log.errorlog("Failed to locate specifications at: " + 
          specLocation + " in plugin " + 
          EscToolsActivator.PLUGIN_ID, ex);
    }
    
    return pluginResource;
  }
  
  /**
   * Install JML JDK specifications as a source folder.
   * 
   * @param project
   * @param sourceFolderName
   * @param location
   */
  public static void installSpecsAsSrcFolder(final IJavaProject project,
                                             final String sourceFolderName, 
                                             final String location) {
    try {
      final IClasspathEntry[] classpath = project.getRawClasspath();
  
      final IFolder f = project.getProject().getFolder(sourceFolderName);
      if (f.exists()) {
        Log.errorlog("Source folder " + sourceFolderName + 
                     " already exists in project " + 
                     project.getElementName(), null);
        return;
      }
      f.createLink(new Path(location), IResource.NONE, null);
      
      final IClasspathEntry[] newClasspath = new IClasspathEntry[classpath.length + 1];
      System.arraycopy(classpath, 0, newClasspath, 0, classpath.length);
      newClasspath[classpath.length] = JavaCore.newSourceEntry(
          f.getFullPath(), 
          new Path[]{new Path("**")});   
          // FIXME - does this exclude the folder from the classpath altogether?
          
      project.setRawClasspath(newClasspath, null);
      // FIXME - the source folder ought to be marked as
      // exported, but there does not seem to be a way to do this
      if (Log.on) {
        Log.log("Installed specs at " + sourceFolderName + " in project " + 
                project.getElementName() + ", location " + location);
      }
       
    } 
    catch (Exception e) {
      Log.errorlog("Failed to install the JML specifications", e);
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
  public static void installSpecsUsingProject(final IJavaProject javaProject,
                                              final String specsProjectName) {
    
    try {
      final IClasspathEntry[] classpath = javaProject.getRawClasspath();  
      for (IClasspathEntry entry: classpath) {
        if (entry.getEntryKind() == IClasspathEntry.CPE_PROJECT) {
          final IPath p = entry.getPath();
          if (p.lastSegment().equals(specsProjectName)) {
            if (Log.on) {
              Log.log("Specs library already installed " + p);
            }
            return;
          }
        }
      }
      
      final IPath specsProject = Utils.getRoot().getFullPath().append(specsProjectName);
  
      final IClasspathEntry[] newClasspath = new IClasspathEntry[classpath.length + 1];
      System.arraycopy(classpath, 0, newClasspath, 0, classpath.length);
      newClasspath[classpath.length] = JavaCore.newProjectEntry(
          specsProject);
      javaProject.setRawClasspath(newClasspath, null);
      if (Log.on) {
        Log.log("Installed specs as project in project " + javaProject.getElementName());
      }

    }
    catch (JavaModelException e) {
      Log.errorlog("Failed to install the JML specifications as a project in " + 
                   javaProject.getElementName(), e);
    }
  }

  /**
   * Create, if it does not already exist, a Java project with the 
   * given name containing a source folder with the given name
   * that links to the given location.  The source folder is
   * entirely excluded from being built but is on the classpath.
   * 
   * @param projectName  The name of the Java project to create
   * @param folder   The name of the source folder in the project
   * @param location     The location (absolute file-system location path) 
   * of the specifications to link to
   * @return  true if the project already existed, false otherwise
   */
  public static boolean installSpecsAsProject(final String projectName,
                                              final String folder, final String location) {
    final IProject project = Utils.getRoot().getProject(projectName);
    String folderName = folder;
    try {
      // Check if the project exists
      if (project.exists()) {
        if (Log.on) {
          Log.log("Specs project already exists - " + projectName);
        }
      } 
      else {
        // It does not exist; create it
        project.create(null);
        project.open(null);
        // Add Java nature to it
        // (expect that it does not have any natures)
        final IProjectDescription description = project.getDescription();
        final String[] ids = description.getNatureIds();
        final String[] newIds = new String[ids.length + 1];
        System.arraycopy(ids, 0, newIds, 0, ids.length);
        newIds[ids.length] = "org.eclipse.jdt.core.javanature";
        description.setNatureIds(newIds);
        project.setDescription(description, null);
      

        final IJavaProject javaProject = JavaCore.create(project);
        if (location.endsWith(".jar")) {
          // The location is a library 
          folderName = JavaVersions.DEFAULT.getSpecsJarfileName(); 
                         // Really a file, not a folder
          final IFile f = project.getFile(folderName);
          f.createLink(new Path(location), IResource.NONE, null);
          // Add the library entry as the only entry to the new classpath
          // (The old classpath has the project as a classpath entry - that has
          // to be left out)
          final IClasspathEntry[] newClasspath = new IClasspathEntry[1];
          newClasspath[0] = JavaCore.newLibraryEntry(
              f.getFullPath(), null, null);
          javaProject.setRawClasspath(newClasspath, null);
        } 
        else {
          // Presume the location is a source folder
          // create the source folder by linking to the specs location
          final IFolder f = project.getFolder(folderName);
          f.createLink(new Path(location), IResource.NONE, null);
                  
          // Add the source entry as the only entry to the new classpath
          // (The old classpath has the project as a classpath entry - that has
          // to be left out)
          final IClasspathEntry[] newClasspath = new IClasspathEntry[1];
          newClasspath[0] = JavaCore.newSourceEntry(
              f.getFullPath(), new Path[]{new Path("**")});
          javaProject.setRawClasspath(newClasspath, null);
          // FIXME - the source folder ought to be marked as
          // exported, but there does not seem to be a way to do this
        }
        
        if (Log.on) {
          Log.log("Installed specs at " + folderName + " in project " + 
                  javaProject.getElementName() + ", location " + location);
        }
          
      }
    } 
    catch (Exception e) {
      Log.errorlog("Failed to install the JML specifications", e);
    }
    return false;
  }

  /**
   * Checks to see whether the given project has the JML system
   * specs on its classpath.
   * @param javaProject The project to check
   * @return  true if the system specs are on the classpath, 
   *       false otherwise
   */
  //@ pure
  public static boolean isSpecsInstalled(final IJavaProject javaProject) {
    // We do this check by taking one file that ought to be in the
    // JML specs and checking to see if it is on the classpath somewhere
    final IPath pp = new Path("java/lang/Object.jml");
    for (String cpe: Utils.getProjectClassPathEntries(javaProject)) {
      final IPath p = new Path(cpe);
      final IResource r = Utils.getRoot().findMember(p);
      if (r instanceof IFolder) {
        if (((IContainer)r).findMember(pp) != null) {
          return true;
        }
      } 
      else if (cpe.endsWith("jmlspecs.jar") ||  cpe.endsWith("escspecs.jar") ||
             JavaVersions.isValidSpecsJar(cpe)) {
        return true;
      }
      // FIXME - should really check if this has 'pp' in it
      //   the above is really a hack
    }
    return false;
  }
  
  /**
   * This method checks to see if the given Java project has 
   * the JML specs linked into it.  If not, then a jmlspecs
   * project containing the JML system and model specs is 
   * created, if it does not already exist.  Finally, the
   * jmlspecs project is added to the classpath of the given
   * project.
   * @param javaProject the project to which we wish to add the jmlspecs project.
   */
  public static void installDefaultSpecs(final IJavaProject javaProject) {
    String location = null;
    try {
      // Check to see if the specs are already linked into the project
      if (isSpecsInstalled(javaProject)) {
        return;
      }
      // If not, find the specs in the plugin
      // FIXME check which version of the specs are installed
      location = findSpecs();
      // Create (if it does not exist) a project and link the specs into it
      installSpecsAsProject(EscjavaPlugin.JMLSPECS_PROJECT_NAME,
          EscjavaPlugin.JMLSPECS_FOLDER_NAME,
          location);
      // Put the new project on the argument project's classpath
      installSpecsUsingProject(javaProject, EscjavaPlugin.JMLSPECS_PROJECT_NAME);
      return;
    } 
    catch (Exception e) {
      Log.errorlog("Failed to install default specs", e);
    }  
    // Try installing as a source folder
    if (location == null) {
      return;
    }
    try {
      installSpecsAsSrcFolder(javaProject, EscjavaPlugin.JMLSPECS_PROJECT_NAME, location);
    }
    catch (Exception e) {
      Log.errorlog("Failed to install default specs as a source folder", e);
    }
  }
  
    


  /**
   * Remove jmlspecs dependencies.
   * 
   * @param project
   */
  public static void removeDefaultSpecs(final IJavaProject project) {
    try {
      // Check to see if the specs are already linked into the project
      if (!isSpecsInstalled(project)) {
        return;
      }
      final IProgressMonitor monitor = null;
      // Remove project on the argument project's classpath
      JavaCore.removeClasspathVariable(EscjavaPlugin.JMLSPECS_PROJECT_NAME, monitor);
      return;
    }
    catch (Exception e) {
      Log.errorlog("Failed to remove dependencies", e);
    }
  }
  

 
  
}
// FIXME - check all javadoc comments

