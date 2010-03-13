/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.typechecker.FormalTypeCheckerVisitor;
import ie.ucd.bon.typechecker.PreliminaryChecker;
import ie.ucd.bon.typechecker.TypeCheckerVisitor;


public final class TypeChecker {

  /** Prevent instantiation of TypeChecker. */
  private TypeChecker() { }

  public static Problems typeCheck(final ParsingTracker tracker, final boolean typeCheck, final boolean checkInformal, final boolean checkFormal, final boolean checkConsistency) {
    Problems allProblems = new Problems("ALLTC");
    
    PreliminaryChecker preCheck = new PreliminaryChecker(tracker.getSymbolTable());
    preCheck.runChecks(checkFormal, checkInformal); //TODO checkConsistency
    allProblems.addProblems(preCheck.getProblems());

    TypeCheckerVisitor visitor = new TypeCheckerVisitor(tracker.getSymbolTable());
    for (ParseResult parse : tracker.getParses()) {
      parse.getParse().accept(visitor);
    }
    allProblems.addProblems(visitor.getProblems());
    
    FormalTypeCheckerVisitor formalTCVisitor = new FormalTypeCheckerVisitor(tracker.getSymbolTable());
    for (ParseResult parse : tracker.getParses()) {
      parse.getParse().accept(formalTCVisitor);
    }
    allProblems.addProblems(formalTCVisitor.getProblems());
    
    return allProblems;
  }

}
