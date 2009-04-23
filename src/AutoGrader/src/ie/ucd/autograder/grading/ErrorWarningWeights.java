package ie.ucd.autograder.grading;

public class ErrorWarningWeights {

  private final double errorWeight;
  private final double warningWeight;
  
  public ErrorWarningWeights(double errorWeight, double warningWeight) {
    super();
    this.errorWeight = errorWeight;
    this.warningWeight = warningWeight;
  }
  
  public double getErrorWeight() {
    return errorWeight;
  }
  public double getWarningWeight() {
    return warningWeight;
  }

  public static final ErrorWarningWeights CHECKSTYLE_WEIGHTS = new ErrorWarningWeights(1,1);
  public static final ErrorWarningWeights PMD_WEIGHTS = new ErrorWarningWeights(1,1);
  public static final ErrorWarningWeights ESCJAVA2_WEIGHTS = new ErrorWarningWeights(1,1);
  public static final ErrorWarningWeights FINDBUGS_WEIGHTS = new ErrorWarningWeights(1,1);
  
}
