/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.errorreporting;

import java.io.PrintStream;
import java.util.Collection;

import com.google.common.collect.TreeMultiset;

public class Problems {

  private final Collection<BONProblem> problems;
  private int numberOfErrors;
  private int numberOfWarnings;
  
  private final String id;
  
  public Problems(String id) {
    problems = TreeMultiset.create();
    numberOfErrors = 0;
    numberOfWarnings = 0;
    this.id = id;
  }
  
  public Problems addProblem(BONProblem problem) {
    //In time filter here...
    problems.add(problem);
    countProblem(problem);
    return this;
  }
  
  public Problems addProblems(Problems newProblems) {
//    System.out.println("Adding " + newProblems.id + " to " + this.id);
    //In time filter here
    this.problems.addAll(newProblems.problems);
    for (BONProblem problem : newProblems.getProblems()) {
      countProblem(problem);
    }
    return this;
  }
  
  private void countProblem(BONProblem problem) {
    if (problem.isError()) {
      numberOfErrors++;
    } else if (problem.isWarning()) {
      numberOfWarnings++;
    }
  }
  
  public Collection<BONProblem> getProblems() {
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

  @Override
  public String toString() {
    return id + "Problems: " + problems.size() + " problems.\n" + problems;
  }
  
  
  
}
