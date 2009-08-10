package ie.ucd.autograder.grading;

import ie.ucd.autograder.util.Pair;
import ie.ucd.autograder.util.Pair.GradeWeightPair;

import java.util.ArrayList;
import java.util.List;

public class AggregateData extends InputData {

  private final List<Pair<InputData,Double>> data;
  
  public AggregateData(String name) {
    super(name, Grade.getPercentageLookup());
    this.data = new ArrayList<Pair<InputData,Double>>();
  }
  
  public void addInputData(InputData input, Double weight) {
    data.add(new Pair<InputData,Double>(input,weight));
  }
  
  public void clearInputData() {
    data.clear();
  }

  @Override
  public Grade getGrade() {
    List<GradeWeightPair> aggregateGrades = new ArrayList<GradeWeightPair>(data.size());
    for (Pair<InputData,Double> item : data) {
      GradeWeightPair pair = new GradeWeightPair(item.getFirst().getGrade(),item.getSecond());
      aggregateGrades.add(pair);
    }
    return Grade.weightedMean(aggregateGrades);
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(getName() + ":\n");
    sb.append(" Overall: " + getGrade() + "\n");
    for (Pair<InputData,Double> d : data) {
      sb.append(d.getFirst().getName() + ": " + d.getFirst().getMeasureAsString() + " (weight: " + d.getSecond() + "), grade:" + d.getFirst().getGrade() + "\n");
    }
    return sb.toString();
  }

  public List<Pair<InputData, Double>> getData() {
    return data;
  }
 
}
