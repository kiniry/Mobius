/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.errorreporting;

import java.io.PrintStream;
import java.util.SortedSet;
import java.util.TreeSet;

public class Problems {

  private final SortedSet<BONProblem> problems;
  private int numberOfErrors;
  private int numberOfWarnings;
  
  public Problems() {
    problems = new TreeSet<BONProblem>();
    numberOfErrors = 0;
    numberOfWarnings = 0;
  }
  
  public void addProblem(BONProblem problem) {
    //In time filter here...
    problems.add(problem);
    countProblem(problem);
  }
  
  public void addProblems(Problems problems) {
    //In time filter here
    this.problems.addAll(problems.getProblems());
    for (BONProblem problem : problems.getProblems()) {
      countProblem(problem);
    }
  }
  
  private void countProblem(BONProblem problem) {
    if (problem.isError()) {
      numberOfErrors++;
    } else if (problem.isWarning()) {
      numberOfWarnings++;
    }
  }
  
  public SortedSet<BONProblem> getProblems() {
    return problems;
  }

  public void printProblems(PrintStream ps) {
    for (BONProblem problem : problems) {
      problem.print(ps);
    }
  }
  
  public void printSummary(PrintStream ps) {
    if (numberOfErrors > 0) {
      ps.println(numberOfErrors + " error" + (numberOfErrors>1 ? "s." : "."));
    } 
    if (numberOfWarnings > 0) {
      ps.println(numberOfWarnings + " warning" + (numberOfWarnings>1 ? "s." : "."));
    }
  }
  
  public boolean testEquality(Problems otherProblems, PrintStream ps) {
    boolean equal = true;
    
    //All problems in this contained in otherProblems?
    for (BONProblem problem : problems) {
      if (!otherProblems.problems.contains(problem)) {
        ps.println("  Error: The following problem was detected but not identified in the test case");
        ps.println("******");
        problem.print(ps);
        ps.println("******");
        equal = false;
      }
    }
    
    //All problems in otherProblems contained in this?
    for (BONProblem problem : otherProblems.problems) {
      if (!problems.contains(problem)) {
        ps.println("  Error: The following problem was not detected");
        ps.println("******");
        problem.print(ps); 
        ps.println("******");
        equal = false;
      }
    }
    
    return equal;
  }

  public int getNumberOfErrors() {
    return numberOfErrors;
  }

  public int getNumberOfWarnings() {
    return numberOfWarnings;
  }
  
  
  
}
