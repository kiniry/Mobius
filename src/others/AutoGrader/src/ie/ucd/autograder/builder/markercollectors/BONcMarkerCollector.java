package ie.ucd.autograder.builder.markercollectors;

import ie.ucd.autograder.grading.AggregateData;
import ie.ucd.autograder.grading.GradeLookupTable;
import ie.ucd.autograder.grading.InputData;
import ie.ucd.autograder.grading.Weights;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class BONcMarkerCollector extends MarkerCollector {

  //Taken from the bonc plugin.xml file
  public static final String BONC_MARKER = "ie.ucd.bon.plugin.bonclocproblemmarker";
  public static final String BONC_MARKER2 = "ie.ucd.bon.plugin.boncproblemmarker";
    
  private static final List<String> types = new ArrayList<String>(2);
  static {
    types.add(BONC_MARKER);
    types.add(BONC_MARKER2);
  }
  
  @Override
  public Collection<String> getTypes() {
    return types;
  }

  @Override
  public String getDataName() {
    return "BONc";
  }

  @Override
  public GradeLookupTable getErrorsLookup() {
    return GradeLookupTable.BONC_ERROR_LOOKUP;
  }

  @Override
  public double getErrorsWeight() {
    return Weights.BONC_WEIGHTS.getErrorWeight();
  }

  @Override
  public GradeLookupTable getWarningsLookup() {
    return GradeLookupTable.BONC_WARNING_LOOKUP;
  }

  @Override
  public double getWarningsWeight() {
    return Weights.BONC_WEIGHTS.getWarningWeight();
  }
  
  @Override
  public double getOverallWeight() {
    return Weights.BONC_WEIGHTS.getOverallWeight();
  }
  
  public AggregateData getAggregateData(double kloc) {
    AggregateData data = new AggregateData(getDataName());
    
    InputData errorData = new InputData("Errors", getErrorsLookup());
    errorData.setMeasure(getAllErrorMarkers().size());
    data.addInputData(errorData, getErrorsWeight());
    
    InputData warningData = new InputData("Warnings", getWarningsLookup());
    warningData.setMeasure(getAllWarningMarkers().size());
    data.addInputData(warningData, getWarningsWeight());
        
    return data; 
  }
}
