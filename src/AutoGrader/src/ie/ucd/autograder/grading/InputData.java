package ie.ucd.autograder.grading;

public class InputData {

  private final String name;
  private double measure;
  private final GradeLookupTable lookup;
  
  public InputData(String name, GradeLookupTable lookup) {
    super();
    this.name = name;
    this.lookup = lookup;
  }
  
  public void setMeasure(double measure) {
    this.measure = measure;
  }
  
  public Grade getGrade() {
    return lookup.toGrade(measure);
  }

  public String getName() {
    return name;
  }

}
