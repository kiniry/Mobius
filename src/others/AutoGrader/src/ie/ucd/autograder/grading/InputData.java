package ie.ucd.autograder.grading;

import java.text.NumberFormat;

public class InputData {

  private final String name;
  private double measure;
  private final GradeLookupTable lookup;
  
  public InputData(String name, GradeLookupTable lookup) {
    super();
    this.name = name;
    this.lookup = lookup;
  }
  
  public InputData setMeasure(double measure) {
    this.measure = measure;
    return this;
  }
  
  public String getMeasureAsString() {
    return "" + format(processMeasure(measure));
  } 
  
  public static final int NUM_DECIMAL_PLACES = 2;
  private static final NumberFormat nf = NumberFormat.getInstance();
  static {
    nf.setMaximumFractionDigits(NUM_DECIMAL_PLACES);
  }
  
  private static String format(double num) {
    return nf.format(num);
  }
  
  public double getMeasure() {
    return measure;
  }

  public Grade getGrade() {
    return lookup.toGrade(processMeasure(measure));
  }
  
  public double getScore(GradeLookupTable converter) {
    return converter.getMarkForGrade(getGrade());
  }

  protected double processMeasure(double measure) {
    return measure;
  }
  
  public String getName() {
    return name;
  }

  public GradeLookupTable getLookup() {
    return lookup;
  }

}
