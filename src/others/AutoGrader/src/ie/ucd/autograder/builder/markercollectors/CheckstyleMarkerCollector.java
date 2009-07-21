package ie.ucd.autograder.builder.markercollectors;

import ie.ucd.autograder.grading.Weights;
import ie.ucd.autograder.grading.GradeLookupTable;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class CheckstyleMarkerCollector extends MarkerCollector {

  //Taken from the eclipse-cs plugin.xml file
  //http://eclipse-cs.cvs.sourceforge.net/viewvc/eclipse-cs/CheckstylePlugin/plugin.xml
  public static final String CHECKSTYLE_MARKER = "com.atlassw.tools.eclipse.checkstyle.CheckstyleMarker";
    
  private static final List<String> types = new ArrayList<String>(1);
  static {
    types.add(CHECKSTYLE_MARKER);
  }
  
  @Override
  public Collection<String> getTypes() {
    return types;
  }

  @Override
  public String getDataName() {
    return "Checkstyle";
  }

  @Override
  public GradeLookupTable getErrorsLookup() {
    return GradeLookupTable.CHECKSTYLE_ERROR_LOOKUP;
  }

  @Override
  public double getErrorsWeight() {
    return Weights.CHECKSTYLE_WEIGHTS.getErrorWeight();
  }

  @Override
  public GradeLookupTable getWarningsLookup() {
    return GradeLookupTable.CHECKSTYLE_WARNING_LOOKUP;
  }

  @Override
  public double getWarningsWeight() {
    return Weights.CHECKSTYLE_WEIGHTS.getWarningWeight();
  }
  
  @Override
  public double getOverallWeight() {
    return Weights.CHECKSTYLE_WEIGHTS.getOverallWeight();
  }
}
