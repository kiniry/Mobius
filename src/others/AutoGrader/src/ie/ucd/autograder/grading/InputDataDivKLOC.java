package ie.ucd.autograder.grading;

public class InputDataDivKLOC extends InputData {
  
  /**
   * The message to be displayed when the number of lines
   * of code is <= 0.
   */
  public static final String NO_CODE_MESSAGE = "no metrics";
  
  private double kloc;
  
  public InputDataDivKLOC(String name, GradeLookupTable lookup) {
    super(name, lookup);
  }

  public void setKLOC(double kloc) {
    this.kloc = kloc;
  }

  @Override
  public String getMeasureAsString() {
    String result = NO_CODE_MESSAGE;
    if (kloc > 0) {
      result = super.getMeasureAsString() + " (Total: " + getMeasure() + ")";
    }
    return result;
  }

  protected double processMeasure(double measure) {
    double result = 0;
    if (kloc > 0) {
      result = measure / kloc;
    }
    return result;
  }
 
  public Grade getGrade() {
    Grade result = Grade.NA;
    if (kloc > 0) {
      result = getLookup().toGrade(processMeasure(getMeasure()));
    }
    return result;
  }
}
