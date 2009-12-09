package ie.ucd.bon.plugin.util;

import ie.ucd.bon.source.SourceLocation;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;

public class PluginUtil {

  private static final boolean IS_WINDOWS = System.getProperty("os.name").toLowerCase().contains("win");
  private static final boolean IS_MAC = System.getProperty("os.name").toLowerCase().startsWith("mac os x");
  
  public static int eclipseAbsoluteCharacterPosition(int absolutePosition, int lineNumber) {
    //Adjusting for different counting of line-ending characters between eclipse and antlr
    if ((IS_WINDOWS) && lineNumber != -1) {
      return absolutePosition + (lineNumber - 1);
    } else {
      return absolutePosition;
    }
  }
  
  public static IMarker createMarker(IProject project, String markerId, SourceLocation location, Map<File,IResource> pathResourceMap, String message, int severity) throws CoreException {

    File file = location == null ? null : location.getSourceFile();
    int lineNumber = location == null ? -1 : location.getLineNumber();
    int charPositionStart = location == null ? -1 : location.getAbsoluteCharPositionStart();
    int charPositionEnd = location == null ? -1 : location.getAbsoluteCharPositionEnd();

    charPositionStart = eclipseAbsoluteCharacterPosition(charPositionStart, lineNumber);
    charPositionEnd = eclipseAbsoluteCharacterPosition(charPositionEnd, lineNumber);

    if (file != null && lineNumber > 0 && charPositionStart >= 0 && charPositionEnd >= 0) {

      IResource resource = pathResourceMap.get(file);
      if (resource != null) {
        IMarker marker = resource.createMarker(markerId);
        marker.setAttribute(IMarker.MESSAGE, message);
        marker.setAttribute(IMarker.LINE_NUMBER, lineNumber);
        marker.setAttribute(IMarker.CHAR_START, charPositionStart);
        marker.setAttribute(IMarker.CHAR_END, charPositionEnd + 1);
        marker.setAttribute(IMarker.SEVERITY, severity);
        return marker;
      }                
      return null;
    } else {
      IMarker marker = project.createMarker(markerId);
      marker.setAttribute(IMarker.MESSAGE, message);
      marker.setAttribute(IMarker.SEVERITY, severity);
      return marker;
    }
  }
  
  /**
   * Computes the classpath (in terms of full absolute file-system paths to
   * directories) from the information available in the Eclipse project.
   * Note that this involves recursively processing the classpath contributions
   * from projects that are on the Eclipse classpath for the requested project.
   *
   * @param project The project whose classpath is to be determined.
   * @return The classpath of the argument in full absolute file-system paths,
   *     separated by the platform's path separator
   */
  public static String getProjectClassPath(final IJavaProject project) {
    final StringBuffer classPath = new StringBuffer(System.getProperty("java.class.path"));
    final List<String> entryList = getProjectClassPathEntries(project);

    for (String entry : entryList) {
      classPath.append(java.io.File.pathSeparator);
      classPath.append(entry);
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
   * @param project the project from which to get the entries.
   * @return List of String containing classpath locations
   */
  public static List<String> getProjectClassPathEntries(final IJavaProject project) {
    final List<String> list = new LinkedList<String>();    
    addResolvedClassPathEntries(list, project, false);
    return list;
  }
  
  /** 
   * TODO
   * FIXME: Ought to use the information that a classpathentry is exported, but the
   * value of cpe.isExported() does not seem to reflect the setting in the Java BuildPath 
   * properties.
   * Thus here we arbitrarily state that only source entries are exported, not
   * libraries or projects.
   * @param list
   * @param project
   * @param onlyExported
   */
  static void addResolvedClassPathEntries(final List<String> list, 
                                          final IJavaProject project,
                                          final boolean onlyExported) {
    try {
      final IClasspathEntry[] classPathEntries = project.getResolvedClasspath(false);
      for (int i = 0; i < classPathEntries.length; ++i) {
        final IClasspathEntry cpe = classPathEntries[i];
        final IPath entry = cpe.getPath();
        final IResource res = ResourcesPlugin.getWorkspace().getRoot().findMember(entry);
        switch (cpe.getEntryKind()) {
          case IClasspathEntry.CPE_LIBRARY:
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
            break;
          case IClasspathEntry.CPE_SOURCE: 
            // The Eclipse documentation is a bit unclear or at odds with
            // the actual behaviour.  What I observe is that
            // - a linked folder gives the same result for getLocation and getRawLocation
            // - a project that is also a source folder gives null for getRawLocation
            // Thus experiment would indicate that getLocation could always be used,
            // but the documentation implies one could always use getRawLocation.  
            // The following code is trying to be conservative. (NOTE)
            if (res.isLinked()) {
              list.add(res.getRawLocation().toOSString());
            } else {
              list.add(res.getLocation().toOSString());
            }
            break;
          case IClasspathEntry.CPE_PROJECT: {
            final IJavaProject jp = JavaCore.create((IProject)res);
            if (jp != null) {
              addResolvedClassPathEntries(list, jp, true);
            } else {
              // FIXME - throw an error of some sort
            }
            break;
          }
          default:
//            Log.errorlog("Unexpected content kind as a classpath entry: " + 
//                         cpe.getEntryKind(), null);
        
        }
      }
    }
    catch (JavaModelException e) {
//      Log.errorlog("Unexpected failure to process the classpath " +
//                   "or project does not have a Java nature: ", e);
    }    
  }
  
  public static Map<File,IResource> getResourceMap(Collection<IResource> resources) {
    Map<File,IResource> map = new HashMap<File,IResource>();
    for (IResource resource : resources) {
      File file = getFile(resource);
      if (file != null) {
        map.put(file, resource);
      }
    }    
    return map;
  }
  
  public static File getFile(IResource resource) {
    IPath path = resource.getLocation();
    if (path != null) {
      File file = path.toFile();
      if (file != null) {
        return file;
      }
    }
    return null;
  }
  
  public static Collection<File> getFiles(Collection<? extends IResource> resources) {
    ArrayList<File> files = new ArrayList<File>();
    for (IResource resource : resources) {
      files.add(getFile(resource));
    }
    return files;
  }
  
}
