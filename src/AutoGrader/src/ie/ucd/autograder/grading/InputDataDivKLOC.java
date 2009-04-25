package ie.ucd.autograder.grading;

public class InputDataDivKLOC extends InputData {

  private double kloc;
  
  public InputDataDivKLOC(String name, GradeLookupTable lookup) {
    super(name, lookup);
  }

  public void setKLOC(double kloc) {
    this.kloc = kloc;
  }

  @Override
  public String getMeasureAsString() {
    return super.getMeasureAsString() + " (Total: " + getMeasure() + ")";
  }

  protected double processMeasure(double measure) {
    return (measure / kloc);
  }
  
}
