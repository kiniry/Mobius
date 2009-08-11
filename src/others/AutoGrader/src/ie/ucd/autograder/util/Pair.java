package ie.ucd.autograder.util;

import ie.ucd.autograder.grading.AggregateData;
import ie.ucd.autograder.grading.Grade;

import java.util.List;

public class Pair <A,B> {

  public final A first;
  public final B second;
  
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
  
  @Override
  public String toString() {
    return "<" + getFirst() + "," + getSecond() + ">";
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
  
  public static class NameProjectDataPair extends Pair<String,List<AggregateData>> {
    public NameProjectDataPair(String first, List<AggregateData> second) {
      super(first, second);
    }
  }
}
