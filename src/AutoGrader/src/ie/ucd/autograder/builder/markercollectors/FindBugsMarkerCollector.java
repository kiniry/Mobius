package ie.ucd.autograder.builder.markercollectors;

import ie.ucd.autograder.grading.Weights;
import ie.ucd.autograder.grading.GradeLookupTable;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class FindBugsMarkerCollector extends MarkerCollector {

  //From de.tobject.findbugs.marker.FindBugsMarker.java
  //http://findbugs.cvs.sourceforge.net/viewvc/findbugs/eclipsePlugin/src/de/tobject/findbugs/marker/FindBugsMarker.java
  public static final String NAME = "edu.umd.cs.findbugs.plugin.eclipse.findbugsMarker";
  public static final String NAME_HIGH = "edu.umd.cs.findbugs.plugin.eclipse.findbugsMarkerHigh";
  public static final String NAME_NORMAL = "edu.umd.cs.findbugs.plugin.eclipse.findbugsMarkerNormal";
  public static final String NAME_LOW = "edu.umd.cs.findbugs.plugin.eclipse.findbugsMarkerLow";
  public static final String NAME_EXPERIMENTAL = "edu.umd.cs.findbugs.plugin.eclipse.findbugsMarkerExperimental";
  
  private static final List<String> types = new ArrayList<String>(5);
  static {
    types.add(NAME);
    //findbugsMarker is the super type of the below, so we can just use it unless we want to ignore some...
//    types.add(NAME_HIGH);
//    types.add(NAME_NORMAL);
//    types.add(NAME_LOW);
//    types.add(NAME_EXPERIMENTAL);
  }
  
  @Override
  public Collection<String> getTypes() {
    return types;
  }

  @Override
  public String getDataName() {
    return "FindBugs";
  }

  @Override
  public GradeLookupTable getErrorsLookup() {
    return GradeLookupTable.FINDBUGS_ERROR_LOOKUP;
  }

  @Override
  public double getErrorsWeight() {
    return Weights.FINDBUGS_WEIGHTS.getErrorWeight();
  }

  @Override
  public GradeLookupTable getWarningsLookup() {
    return GradeLookupTable.FINDBUGS_WARNING_LOOKUP;
  }

  @Override
  public double getWarningsWeight() {
    return Weights.FINDBUGS_WEIGHTS.getWarningWeight();
  }

  @Override
  public double getOverallWeight() {
    return Weights.FINDBUGS_WEIGHTS.getOverallWeight();
  }
  
  
}
