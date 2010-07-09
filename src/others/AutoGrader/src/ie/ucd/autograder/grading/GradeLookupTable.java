package ie.ucd.autograder.grading;

import ie.ucd.autograder.util.Log;
import ie.ucd.autograder.util.Pair.MarkGradePair;

import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class GradeLookupTable {

  private final List<MarkGradePair> gradeBoundaries;
  private final Map<Grade,Double> gradeMarkMap;
  
  public GradeLookupTable(MarkGradePair[] gradeBoundaries) {
    this(Arrays.asList(gradeBoundaries));
  }

  public GradeLookupTable(List<MarkGradePair> gradeBoundaries) {
    this.gradeBoundaries = gradeBoundaries;
    Collections.sort(gradeBoundaries, new Comparator<MarkGradePair>() {
      public int compare(MarkGradePair o1, MarkGradePair o2) {
        return o2.getFirst().compareTo(o1.getFirst());
      }
    });
    
    //TODO check valid list of grade boundaries. Final boundary should be zero.
    
    gradeMarkMap = new HashMap<Grade,Double>(gradeBoundaries.size());
    for (MarkGradePair pair : gradeBoundaries) {
      gradeMarkMap.put(pair.second, pair.first);
    }
  }

  public Grade toGrade(double mark) {

    for (MarkGradePair boundary : gradeBoundaries) {
      if (mark >= boundary.getFirst()) {
        return boundary.getSecond();
      }
    }
    Log.error("No grade found for mark " + mark + 
              "!\n Boundaries: " + gradeBoundaries);
    assert false; //Final boundary should always have a mark of zero!
    return null;
  }

  public double getMarkForGrade(Grade grade) {
    Double d = gradeMarkMap.get(grade);
    if (d == null) {
      // Log.info("No mark for grade " + grade + " in table " + toString());
      return 0.0;
    } else {
      return d;
    }
  }
  
  public double getMarkForGrade(String gradeName) {
    return getMarkForGrade(Grade.gradeFromStringName(gradeName));
  }
  
  public String toString() {
    StringBuilder sb = new StringBuilder();
    for (MarkGradePair pair : gradeBoundaries) {
      sb.append(pair.second + "," + pair.first + ";");
    }    
    return sb.toString();
  }
  
}
