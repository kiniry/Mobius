package ie.ucd.autograder.util;

import ie.ucd.autograder.grading.Grade;

public class Pair <A,B> {

  private final A first;
  private final B second;
  
  public Pair(A first, B second) {
    this.first = first;
    this.second = second;
  }

  public A getFirst() {
    return first;
  }

  public B getSecond() {
    return second;
  }
  
  public static class MarkGradePair extends Pair<Double,Grade> {
    public MarkGradePair(Double first, Grade second) {
      super(first, second);
    }
  }
  
  public static class GradeWeightPair extends Pair<Grade,Double> {
    public GradeWeightPair(Grade first, Double second) {
      super(first, second);
    }
  }
}
