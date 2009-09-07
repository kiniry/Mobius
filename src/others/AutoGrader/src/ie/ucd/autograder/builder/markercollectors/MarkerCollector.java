package ie.ucd.autograder.builder.markercollectors;

import ie.ucd.autograder.grading.AggregateData;
import ie.ucd.autograder.grading.GradeLookupTable;
import ie.ucd.autograder.grading.InputData;
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

public class MarkerCollector {

  private final Map<String,List<IMarker>> markersMap;
  
  private final String name;
  private final Collection<String> types;
  private final float weight;
  private final boolean divKLoc;
  private final boolean errorsEnabled;
  private final boolean warningsEnabled;
  private final float errorsWeight;
  private final float warningsWeight;
  private final GradeLookupTable errorsLookup;
  private final GradeLookupTable warningsLookup;
  
  public MarkerCollector(String name, Collection<String> types, float weight, boolean divKLoc, 
      boolean errorsEnabled, float errorsWeight, GradeLookupTable errorsLookup,
      boolean warningsEnabled, float warningsWeight, GradeLookupTable warningsLookup) {
    markersMap = new HashMap<String,List<IMarker>>();
    this.name = name;
    this.types = types;
    this.weight = weight;
    this.divKLoc = divKLoc;
    this.errorsEnabled = errorsEnabled;
    this.errorsWeight = errorsWeight;
    this.errorsLookup = errorsLookup;
    this.warningsEnabled = warningsEnabled;
    this.warningsWeight = warningsWeight;
    this.warningsLookup = warningsLookup;
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
  
  public Collection<String> getTypes() {
    return types;
  }
  
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
  
  public AggregateData getAggregateData(double kloc, GradeLookupTable table) {
    AggregateData data = new AggregateData(getDataName(), table, false);
    
    InputData errorData;
    if (divKLoc) {
      InputDataDivKLOC errorData2 = new InputDataDivKLOC("Errors per KLOC", getErrorsLookup());
      errorData2.setKLOC(kloc);
      errorData = errorData2;
    } else {
      errorData = new InputData("Errors", getErrorsLookup());
    }
    errorData.setMeasure(getAllErrorMarkers().size());
    data.addInputData(errorData, getErrorsWeight());
    
    InputData warningData;
    if (divKLoc) {
      InputDataDivKLOC warningData2 = new InputDataDivKLOC("Warnings per KLOC", getWarningsLookup());
      warningData2.setKLOC(kloc);
      warningData = warningData2;
    } else {
      warningData = new InputData("Warnings", getWarningsLookup());
    }
    
    warningData.setMeasure(getAllWarningMarkers().size());
    data.addInputData(warningData, getWarningsWeight());
        
    return data; 
  }
  
  public String getDataName() {
    return name;
  }
  
  public GradeLookupTable getWarningsLookup() {
    return warningsLookup;
  }
  
  public double getWarningsWeight() {
    return warningsWeight;
  }
  
  public GradeLookupTable getErrorsLookup() {
    return errorsLookup;
  }
  
  public double getErrorsWeight() {
    return errorsWeight;
  }
  
  public double getOverallWeight() {
    return weight;
  }

  public boolean isErrorsEnabled() {
    return errorsEnabled;
  }

  public boolean isWarningsEnabled() {
    return warningsEnabled;
  }
  
}
