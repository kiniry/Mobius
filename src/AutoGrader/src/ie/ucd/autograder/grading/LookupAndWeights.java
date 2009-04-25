package ie.ucd.autograder.grading;

import static ie.ucd.autograder.grading.Weights.CHECKSTYLE_WEIGHTS;
import static ie.ucd.autograder.grading.Weights.ESCJAVA2_WEIGHTS;
import static ie.ucd.autograder.grading.Weights.FINDBUGS_WEIGHTS;
import static ie.ucd.autograder.grading.Weights.PMD_WEIGHTS;
import static ie.ucd.autograder.grading.GradeLookupTable.CHECKSTYLE_ERROR_LOOKUP;
import static ie.ucd.autograder.grading.GradeLookupTable.CHECKSTYLE_WARNING_LOOKUP;
import static ie.ucd.autograder.grading.GradeLookupTable.ESCJAVA2_ERROR_LOOKUP;
import static ie.ucd.autograder.grading.GradeLookupTable.ESCJAVA2_WARNING_LOOKUP;
import static ie.ucd.autograder.grading.GradeLookupTable.FINDBUGS_ERROR_LOOKUP;
import static ie.ucd.autograder.grading.GradeLookupTable.FINDBUGS_WARNING_LOOKUP;
import static ie.ucd.autograder.grading.GradeLookupTable.PMD_ERROR_LOOKUP;
import static ie.ucd.autograder.grading.GradeLookupTable.PMD_WARNING_LOOKUP;
import ie.ucd.autograder.util.Pair.GradeWeightPair;

public class LookupAndWeights {

  private final Weights weights;
  private final GradeLookupTable errorLookup;
  private final GradeLookupTable warningLookup;
  
  public LookupAndWeights(GradeLookupTable errorLookup, GradeLookupTable warningLookup, Weights weights) {
    super();
    this.errorLookup = errorLookup;
    this.warningLookup = warningLookup;
    this.weights = weights;
  }
  
  public Weights getWeights() {
    return weights;
  }
  
  public GradeLookupTable getErrorLookup() {
    return errorLookup;
  }

  public GradeLookupTable getWarningLookup() {
    return warningLookup;
  }
  
  public Grade getGrade(double errorCount, double warningCount) {
    return Grade.weightedMean(
        new GradeWeightPair(errorLookup.toGrade(errorCount), weights.getErrorWeight()),
        new GradeWeightPair(errorLookup.toGrade(warningCount), weights.getWarningWeight())
        );
  }

  public static final LookupAndWeights CHECKSTYLE = new LookupAndWeights(CHECKSTYLE_ERROR_LOOKUP, CHECKSTYLE_WARNING_LOOKUP, CHECKSTYLE_WEIGHTS);
  public static final LookupAndWeights FINDBUGS = new LookupAndWeights(FINDBUGS_ERROR_LOOKUP, FINDBUGS_WARNING_LOOKUP, FINDBUGS_WEIGHTS);
  public static final LookupAndWeights ESCJAVA2 = new LookupAndWeights(ESCJAVA2_ERROR_LOOKUP, ESCJAVA2_WARNING_LOOKUP, ESCJAVA2_WEIGHTS);
  public static final LookupAndWeights PMD = new LookupAndWeights(PMD_ERROR_LOOKUP, PMD_WARNING_LOOKUP, PMD_WEIGHTS);
  
}
