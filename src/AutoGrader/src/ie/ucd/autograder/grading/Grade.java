package ie.ucd.autograder.grading;

import ie.ucd.autograder.util.Pair;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;


public enum Grade {

  A_PLUS("A+", 90), A("A", 85), A_MINUS("A-", 80),
  B_PLUS("B+", 75), B("B", 70), B_MINUS("B-", 65),
  C_PLUS("C+", 60), C("C", 55), C_MINUS("C-", 50),
  D_PLUS("D+", 45), D("D", 40), D_MINUS("D-", 35),
  E_PLUS("E+", 30), E("E", 25), E_MINUS("E-", 20),
  F("F", 10), NG("NG", 0);
  
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

