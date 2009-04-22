package ie.ucd.autograder.grading;

import ie.ucd.autograder.util.Pair;

import java.util.List;

public class GradeLookupTable {

  private final List<Pair<Double,Grade>> gradeBoundaries;
  
  public GradeLookupTable(List<Pair<Double,Grade>> gradeBoundaries) {
    this.gradeBoundaries = gradeBoundaries;
  }
  
  public Grade toGrade(double mark) {
    
    for (Pair<Double,Grade> boundary : gradeBoundaries) {
      if (mark > boundary.getFirst()) {
        return boundary.getSecond();
      }
    }
    assert false; //Final boundary should always have a mark of zero!
    return null;
  }
  
}
