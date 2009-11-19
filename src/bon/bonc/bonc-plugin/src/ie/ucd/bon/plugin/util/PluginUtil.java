package ie.ucd.bon.plugin.util;

import ie.ucd.bon.source.SourceLocation;

import java.io.File;
import java.util.Map;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

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
  
  public static IMarker createMarker(IProject project, String markerId, SourceLocation location, Map<String,IResource> pathResourceMap, String message, int severity) throws CoreException {

    File file = location == null ? null : location.getSourceFile();
    int lineNumber = location == null ? -1 : location.getLineNumber();
    int charPositionStart = location == null ? -1 : location.getAbsoluteCharPositionStart();
    int charPositionEnd = location == null ? -1 : location.getAbsoluteCharPositionEnd();

    charPositionStart = eclipseAbsoluteCharacterPosition(charPositionStart, lineNumber);
    charPositionEnd = eclipseAbsoluteCharacterPosition(charPositionEnd, lineNumber);

    //System.out.println("File: " + file + ", line: " + lineNumber + ", char: (" + charPositionStart + ", " + charPositionEnd + ")");

    if (file != null && lineNumber > 0 && charPositionStart >= 0 && charPositionEnd >= 0) {

      IResource resource = pathResourceMap.get(file.getAbsolutePath());
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
      //For the moment nothing.
      //TODO - how best to show an error without an associated location?
      IMarker marker = project.createMarker(markerId);
      marker.setAttribute(IMarker.MESSAGE, message);
      marker.setAttribute(IMarker.SEVERITY, severity);
      return marker;
    }
  }
  
}
