package ie.ucd.autograder.grading;

import ie.ucd.autograder.util.Pair.GradeWeightPair;
import ie.ucd.autograder.util.Pair.MarkGradePair;

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
  G("G", 0.03), NG("NG", 0), NA("N/A", -1);

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
  public static GradeLookupTable getPercentageLookup() {
    if (percentageLookup == null) {
      List<MarkGradePair> list = new ArrayList<MarkGradePair>(values().length);
      for (Grade grade : values()) {
        list.add(new MarkGradePair(grade.getMark(), grade));
      }
      percentageLookup = new GradeLookupTable(list);
    }
    return percentageLookup;
  }

  //Lookup for converting a percentage back to a grade
  private static GradeLookupTable NALookup = null;
  public static GradeLookupTable getNALookup() {
    if (NALookup == null) {
      List<MarkGradePair> list = new ArrayList<MarkGradePair>(1);
      list.add(new MarkGradePair(NA.mark, NA));
      NALookup = new GradeLookupTable(list);
    }
    return NALookup;
  }

  public static Grade mean(Grade... grades) {
    return mean(Arrays.asList(grades));
  }

  public static Grade mean(Collection<Grade> grades) {
    return getPercentageLookup().toGrade(meanAsDouble(grades));
  }

  public static double meanAsDouble(Collection<Grade> grades) {
    double denom = grades.size();
    double num = 0;
    for (Grade grade : grades) {
      num += grade.getMark();
    }
    return num / denom;
  }

  public static Grade weightedMean(GradeWeightPair... grades) {
    return weightedMean(Arrays.asList(grades));
  }

  public static Grade weightedMean(Collection<GradeWeightPair> grades) {
    return getPercentageLookup().toGrade(weightedMeanAsDouble(grades));
  }

  public static double weightedMeanAsDouble(Collection<GradeWeightPair> grades) {
    double totalWeight = 0;
    double total = 0;
    
    for (GradeWeightPair grade : grades) {
//      System.out.println("GradeWeightPair: " + grade);
      totalWeight += grade.getSecond();
    }
    
    if (total == 0) {
//      System.out.println("Total is zero");
      return 0;
    }
    
    return total / totalWeight;
  }
}

