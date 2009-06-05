/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.typechecker.FormalTypeChecker;
import ie.ucd.bon.typechecker.PreliminaryChecker;
import ie.ucd.bon.typechecker.informal.InformalTypeChecker;

import org.antlr.runtime.RecognitionException;


public final class TypeChecker {

  /** Prevent instantiation of TypeChecker. */
  private TypeChecker() { }

  public static void typeCheck(final ParsingTracker tracker, final boolean typeCheck, final boolean checkInformal, final boolean checkFormal, final boolean checkConsistency) throws RecognitionException {
    //TODO fix!
//    InformalTypeChecker itc = tracker.getInformalTypeChecker();
//    FormalTypeChecker ftc = tracker.getFormalTypeChecker();
//    
//    if (checkInformal) {
//      Main.logDebug("Checking informal");
//      itc.performPreliminaryChecks();
//    }
//    
//    if (checkFormal) {
//      Main.logDebug("Checking formal");
//      ftc.performPreliminaryChecks();
//    }
//    
//    if (checkConsistency) {
//      Main.logDebug("Checking consistency");
//      //TODO better way than passing ITI in here?
//      ftc.performLevelConsistencyChecks(tracker.getTypingInformation().informal());
//    }
//    
//    if (typeCheck) {
//      for (ParseResult parse : tracker.getParses()) {
//        typeCheck(parse, itc, ftc);
//      }
//    } else {
//      Main.logDebug("Not typechecking");
//    }
    
    PreliminaryChecker preCheck = new PreliminaryChecker(tracker.getSymbolTable());
    preCheck.runChecks(checkFormal, checkInformal);
    tracker.addProblems(preCheck.getProblems());
  }
  
  public static void typeCheck(final ParseResult parse, final InformalTypeChecker itc, final FormalTypeChecker ftc) throws RecognitionException {
    Main.logDebug("Typechecking " + parse.getFilePath());
    
    //TODO fix!
    
//    CommonTree t = (CommonTree)parse.getParse().getTree(); //Get input tree
//    CommonTreeNodeStream nodes = new CommonTreeNodeStream(t);  //Get stream of nodes from tree
//    nodes.setTokenStream(parse.getTokens());
//
//    walker.initialise(nodes, itc, ftc, parse.getFile()); //Reset walker, provide inputs
//
//    walker.prog();  //Walk    
  }
  
}
