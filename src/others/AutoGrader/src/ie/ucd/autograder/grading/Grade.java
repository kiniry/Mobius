package ie.ucd.autograder.grading;

import ie.ucd.autograder.util.Pair.GradeWeightPair;
import ie.ucd.autograder.util.Pair.MarkGradePair;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public enum Grade {

  A_PLUS("A+"), A("A"), A_MINUS("A-"),
  B_PLUS("B+"), B("B"), B_MINUS("B-"),
  C_PLUS("C+"), C("C"), C_MINUS("C-"),
  D_PLUS("D+"), D("D"), D_MINUS("D-"),
  E_PLUS("E+"), E("E"), E_MINUS("E-"),
  F_PLUS("F+"), F("F"), F_MINUS("F-"),
  G("G"), NG("NG"), NA("N/A");

  private final String grade;
  private Grade(String grade) {
    this.grade = grade;
  }
  
  public static Grade gradeFromStringName(String name) {
    for (Grade grade : Grade.values()) {
      if (grade.grade.equals(name)) {
        return grade;
      }
    }
    //TODO throw exception?
    return NA;
  }

  @Override
  public String toString() {
    return grade;
  }

  //Lookup for converting a percentage back to a grade
  private static GradeLookupTable NALookup = null;
  public static GradeLookupTable getNALookup() {
    if (NALookup == null) {
      List<MarkGradePair> list = new ArrayList<MarkGradePair>(1);
      list.add(new MarkGradePair(0.0, NA));
      NALookup = new GradeLookupTable(list);
    }
    return NALookup;
  }

  public static double weightedMeanAsDouble(Collection<GradeWeightPair> grades, GradeLookupTable table) {
    double totalWeight = 0;
    double total = 0;
    
    for (GradeWeightPair pair : grades) {
      total += table.getMarkForGrade(pair.first) * pair.second;
      totalWeight += pair.getSecond();
    }
    
    if (totalWeight == 0) {
      return 0;
    }
    
    return total / totalWeight;
  }
}

