package ie.ucd.autograder.builder.markercollectors;

import ie.ucd.autograder.grading.AggregateData;
import ie.ucd.autograder.grading.GradeLookupTable;
import ie.ucd.autograder.grading.InputDataDivKLOC;

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
    //System.out.println("Found " + markers.length + " markers of type " + type);
    addMarkers(type, markers);
  }
  
  public void clearMarkers(String type) {
    markersMap.put(type, new LinkedList<IMarker>());
  }
  
  public List<IMarker> getMarkers(String type) {
    return markersMap.get(type);
  }
  
  public List<IMarker> getAllMarkers() {
    List<IMarker> total = new LinkedList<IMarker>();
    for (List<IMarker> list : markersMap.values()) {
      total.addAll(list);
    }
    return total;
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
  
  public List<IMarker> getAllWarningMarkers() {
    return getWarnings(getAllMarkers());
  }
  
  public List<IMarker> getAllErrorMarkers() {
    return getErrors(getAllMarkers());
  }
  
  public List<IMarker> getAllInfoMarkers() {
    return getInfos(getAllMarkers());
  }  
  
  private static final int DEFAULT_SEVERITY = IMarker.SEVERITY_ERROR;
  
  public static List<IMarker> getWarnings(List<IMarker> markers) {
    return filterByAttribute(markers, IMarker.SEVERITY, IMarker.SEVERITY_WARNING, DEFAULT_SEVERITY);    
  }
  
  public static List<IMarker> getErrors(List<IMarker> markers) {
    return filterByAttribute(markers, IMarker.SEVERITY, IMarker.SEVERITY_ERROR, DEFAULT_SEVERITY);    
  }
  
  public static List<IMarker> getInfos(List<IMarker> markers) {
    return filterByAttribute(markers, IMarker.SEVERITY, IMarker.SEVERITY_INFO, DEFAULT_SEVERITY);    
  }
  
  private static List<IMarker> filterByAttribute(List<IMarker> markers, String attribute, int filterValue, int defaultValue) {
    List<IMarker> filteredList = new LinkedList<IMarker>();
    for (IMarker marker : markers) {
      if (marker.getAttribute(attribute, defaultValue) == filterValue) {
        filteredList.add(marker);
      }
    }
    return filteredList;
  }
  
  public AggregateData getAggregateData(double kloc) {
    AggregateData data = new AggregateData(getDataName());
    
    InputDataDivKLOC errorData = new InputDataDivKLOC("Errors per KLOC", getErrorsLookup());
    errorData.setKLOC(kloc);
    errorData.setMeasure(getAllErrorMarkers().size());
    data.addInputData(errorData, getErrorsWeight());
    
    InputDataDivKLOC warningData = new InputDataDivKLOC("Warnings per KLOC", getWarningsLookup());
    warningData.setKLOC(kloc);
    warningData.setMeasure(getAllWarningMarkers().size());
    data.addInputData(warningData, getWarningsWeight());
        
    return data; 
  }
  
  public abstract String getDataName();
  public abstract GradeLookupTable getWarningsLookup();
  public abstract double getWarningsWeight();
  public abstract GradeLookupTable getErrorsLookup();
  public abstract double getErrorsWeight();
  public abstract double getOverallWeight();
}
