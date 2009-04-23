package ie.ucd.autograder.grading;

public interface ConfigurationConstants {

  static final double WEIGHT_CHECKSTYLE = 1;
  static final double WEIGHT_ESCJAVA2 = 1;
  static final double WEIGHT_FINDBUGS = 1;
  static final double WEIGHT_PMD = 1;
  static final double WEIGHT_METRICS = 1;
  
  static final double CHECKSTYLE_WEIGHT_ERRORS = 1;
  static final double CHECKSTYLE_WEIGHT_WARNINGS = 1;
  static final double CHECKSTYLE_WEIGHT_INFO = 1;
  
  static final double PMD_WEIGHT_OBJECTNCSS = 1;
  static final double PMD_WEIGHT_OBJECTFUNCTIONS = 1;
  static final double PMD_WEIGHT_OBJECTINNERCLASSES = 1;
  static final double PMD_WEIGHT_OBJECTJAVADOCCOMMENTS = 1;
  static final double PMD_WEIGHT_AVERAGEFUNCTIONNCSS = 1;
  static final double PMD_WEIGHT_AVERAGEFUNCTIONCCN = 1;
  static final double PMD_WEIGHT_AVERAGEFUNCTIONJVDC = 1;

}