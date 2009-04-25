package ie.ucd.autograder.builder.markercollectors;

import ie.ucd.autograder.grading.Weights;
import ie.ucd.autograder.grading.GradeLookupTable;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class PMDMarkerCollector extends MarkerCollector {

  //Taken from the PMD eclipse plugin.xml file
  //http://pmd.svn.sourceforge.net/viewvc/pmd/trunk/pmd-eclipse-plugin/plugins/net.sourceforge.pmd.eclipse.plugin/plugin.xml
  public static final String PMD_MARKER = "net.sourceforge.pmd.eclipse.plugin.pmdMarker";
  public static final String PMD_TASK_MARKER = "net.sourceforge.pmd.eclipse.plugin.pmdTaskMarker";
  public static final String PMD_DFA_MARKER = "net.sourceforge.pmd.eclipse.plugin.pmdDFAMarker";
  
  private static final List<String> types = new ArrayList<String>(3);
  static {
    types.add(PMD_MARKER);
//    Not sure what the below two are for...
    types.add(PMD_TASK_MARKER);
    types.add(PMD_DFA_MARKER);
  }
  
  @Override
  public Collection<String> getTypes() {
    return types;
  }

  @Override
  public String getDataName() {
    return "PMD";
  }

  @Override
  public GradeLookupTable getErrorsLookup() {
    return GradeLookupTable.PMD_ERROR_LOOKUP;
  }

  @Override
  public double getErrorsWeight() {
    return Weights.PMD_WEIGHTS.getErrorWeight();
  }

  @Override
  public GradeLookupTable getWarningsLookup() {
    return GradeLookupTable.PMD_WARNING_LOOKUP;
  }

  @Override
  public double getWarningsWeight() {
    return Weights.PMD_WEIGHTS.getWarningWeight();
  }

  @Override
  public double getOverallWeight() {
    return Weights.PMD_WEIGHTS.getOverallWeight();
  }
  
}
