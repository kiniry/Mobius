package ie.ucd.autograder.grading;

import ie.ucd.autograder.util.Pair;
import ie.ucd.autograder.util.Pair.GradeWeightPair;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

public class AggregateData extends InputData {

  private final List<Pair<InputData,Double>> data;
  
  public AggregateData(String name) {
    super(name, Grade.getPercentageLookup());
    this.data = new LinkedList<Pair<InputData,Double>>();
  }
  
  public void addInputData(InputData input, Double weight) {
    data.add(new Pair<InputData,Double>(input,weight));
  }

  @Override
  public Grade getGrade() {
    List<GradeWeightPair> aggregateGrades = new ArrayList<GradeWeightPair>(data.size());
    for (Pair<InputData,Double> item : data) {
      aggregateGrades.add(new GradeWeightPair(item.getFirst().getGrade(),item.getSecond()));
    }
    return Grade.weightedMean(aggregateGrades);
  }
  
}
