package ie.ucd.autograder.grading;

public class Weights {

  private final double overallWeight;
  private final double errorWeight;
  private final double warningWeight;
  
  public Weights(double overallWeight, double errorWeight, double warningWeight) {
    super();
    this.overallWeight = overallWeight;
    this.errorWeight = errorWeight;
    this.warningWeight = warningWeight;
  }
  
  public double getErrorWeight() {
    return errorWeight;
  }
  
  public double getWarningWeight() {
    return warningWeight;
  }

  public double getOverallWeight() {
    return overallWeight;
  }

  public static final Weights CHECKSTYLE_WEIGHTS = new Weights(1,1,1);
  public static final Weights BONC_WEIGHTS = new Weights(1,1,1);
  public static final Weights PMD_WEIGHTS = new Weights(1,1,1);
  public static final Weights ESCJAVA2_WEIGHTS = new Weights(1,1,1);
  public static final Weights FINDBUGS_WEIGHTS = new Weights(1,1,1);
  
}
