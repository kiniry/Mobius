package ie.ucd.bon.typechecker;

import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.typechecker.informal.errors.SystemNotDefinedError;

public class PreliminaryChecker {

  private final Problems problems;
  private final BONST st;
  
  public PreliminaryChecker(BONST st) {
    problems = new Problems("Prelim");
    this.st = st;
  }

  public Problems getProblems() {
    return problems;
  }
  
  public void runChecks(boolean checkFormal, boolean checkInformal) {
    if (checkFormal) {
      
    }
    
    if (checkInformal) {
      checkSystemDefined();
    }
    
  }
  
  public void checkSystemDefined() {
    if (st.informal.systemChart == null) {
      problems.addProblem(new SystemNotDefinedError());
    }
  }
  
}
