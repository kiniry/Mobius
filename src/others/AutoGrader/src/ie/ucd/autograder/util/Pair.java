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
  
  @SuppressWarnings("unchecked")
  @Override
  public boolean equals(Object obj) {
    if (obj instanceof Pair) {
      Pair<?,?> pair = (Pair<?,?>)obj;
      Object obj1 = pair.getFirst();
      Object obj2 = pair.getSecond();
      if (first == null && obj1 != null) {
        return false;
      }
      if (second == null && obj2 != null) {
        return false;
      }
      return first.equals(obj1) && second.equals(obj2);
    } else {
      return false;
    }
    
  }

  @Override
  public int hashCode() {
    int hash1 = first == null ? 1 : first.hashCode();
    int hash2 = second == null ? 1 : second.hashCode();
    return hash1 * hash2;
  }

  @Override
  public String toString() {
    return "<" + getFirst() + "," + getSecond() + ">";
  }

  public static class MarkGradePair extends Pair<Double,Grade> {
    public MarkGradePair(Double mark, Grade grade) {
      super(mark, grade);
    }
  }
  
  public static class GradeWeightPair extends Pair<Grade,Double> {
    public GradeWeightPair(Grade grade, Double weight) {
      super(grade, weight);
    }
  }
  
  public static class NameProjectDataPair extends Pair<String,List<AggregateData>> {
    public NameProjectDataPair(String name, List<AggregateData> projectData) {
      super(name, projectData);
    }
  }
}
