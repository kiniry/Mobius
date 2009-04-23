package ie.ucd.autograder.grading;

import ie.ucd.autograder.util.Pair;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;


public enum Grade {

  A_PLUS("A+", 78.33), A("A", 75), A_MINUS("A-", 71.66),
  B_PLUS("B+", 68.33), B("B", 65), B_MINUS("B-", 61.66),
  C_PLUS("C+", 58.33), C("C", 55), C_MINUS("C-", 51.66),
  D_PLUS("D+", 48.33), D("D", 45), D_MINUS("D-", 41.66),
  E_PLUS("E+", 38.33), E("E", 35), E_MINUS("E-", 31.66),
  F_PLUS("F+", 28.33), F("F", 25), F_MINUS("F-", 21.66),
  G("G", 0.03), NG("NG", 0);
  
  private final String grade;
  private final double mark;
  private Grade(String grade, double mark) {
    this.grade = grade;
    this.mark = mark;
  }
  
  @Override
  public String toString() {
    return grade;
  }
  
  public double getMark() {
    return mark;
  }
  
  //Lookup for converting a percentage back to a grade
  private static GradeLookupTable percentageLookup = null;
  private static GradeLookupTable getPercentageLookup() {
    if (percentageLookup == null) {
      List<Pair<Double,Grade>> list = new ArrayList<Pair<Double,Grade>>(values().length);
      for (Grade grade : values()) {
        list.add(new Pair<Double,Grade>(grade.getMark(), grade));
      }
    }
    return percentageLookup;
  }
  
  public static Grade average(Grade... grades) {
    return average(Arrays.asList(grades));
  }
  
  public static Grade average(Collection<Grade> grades) {
    return getPercentageLookup().toGrade(averageAsDouble(grades));
  }
  
  public static double averageAsDouble(Collection<Grade> grades) {
    double denom = grades.size();
    double num = 0;
    for (Grade grade : grades) {
      num += grade.getMark();
    }
    return num / denom;
  }
}

