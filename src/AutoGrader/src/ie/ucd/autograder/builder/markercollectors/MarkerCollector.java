package ie.ucd.autograder.builder.markercollectors;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

public abstract class MarkerCollector {

  private Map<String,List<IMarker>> markersMap;
  
  public MarkerCollector() {
    markersMap = new HashMap<String,List<IMarker>>();
  }
  
  public void addMarkers(String type, IMarker[] markersToAdd) {
    List<IMarker> markers = markersMap.get(type);
    if (markers == null) {
      markers = new LinkedList<IMarker>();
      markersMap.put(type, markers);
    }
    markers.addAll(Arrays.asList(markersToAdd));
  }
  
  public void addMarkers(IProject project, String type) throws CoreException {
    IMarker[] markers = project.findMarkers(type, true, IResource.DEPTH_INFINITE);
    System.out.println("Found " + markers.length + " markers of type " + type);
    addMarkers(type, markers);
  }
  
  public void clearMarkers(String type) {
    markersMap.put(type, new LinkedList<IMarker>());
  }
  
  public List<IMarker> getMarkers(String type) {
    return markersMap.get(type);
  }
  
  public abstract Collection<String> getTypes();
  
  public void addMarkers(IProject project) throws CoreException {
    for (String type : getTypes()) {
      addMarkers(project, type);
    }
  }
  
  public void clearAllMarkers() {
    for (String type : getTypes()) {
      clearMarkers(type);
    }
  }
  
}
