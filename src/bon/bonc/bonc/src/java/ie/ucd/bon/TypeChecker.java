/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.typechecker.PreliminaryChecker;
import ie.ucd.bon.typechecker.TypeCheckerVisitor;


public final class TypeChecker {

  /** Prevent instantiation of TypeChecker. */
  private TypeChecker() { }

  public static Problems typeCheck(final ParsingTracker tracker, final boolean typeCheck, final boolean checkInformal, final boolean checkFormal, final boolean checkConsistency) {
    PreliminaryChecker preCheck = new PreliminaryChecker(tracker.getSymbolTable());
    preCheck.runChecks(checkFormal, checkInformal); //TODO checkConsistency

    TypeCheckerVisitor visitor = new TypeCheckerVisitor(tracker.getSymbolTable());
    for (ParseResult parse : tracker.getParses()) {
      parse.getParse().accept(visitor);
    }
    return visitor.getProblems().addProblems(preCheck.getProblems());
  }

}
