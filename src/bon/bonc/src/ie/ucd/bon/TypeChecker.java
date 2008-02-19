/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.parser.BONTCTreeWalker;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.typechecker.FormalTypeChecker;
import ie.ucd.bon.typechecker.informal.InformalTypeChecker;

import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.CommonTree;
import org.antlr.runtime.tree.CommonTreeNodeStream;


public class TypeChecker {

  private static final BONTCTreeWalker walker = new BONTCTreeWalker(null);
  
  public static void typeCheck(ParsingTracker tracker, boolean checkInformal, boolean checkFormal, boolean checkConsistency) throws RecognitionException {
    InformalTypeChecker itc = tracker.getInformalTypeChecker();
    FormalTypeChecker ftc = tracker.getFormalTypeChecker();
    
    if (checkInformal) {
      Main.logDebug("Checking informal");
      itc.performPreliminaryChecks();
    }
    
    if (checkFormal) {
      Main.logDebug("Checking formal");
      ftc.performPreliminaryChecks();
    }
    
    if (checkConsistency) {
      Main.logDebug("Checking consistency");
      //TODO better way than passing ITI in here?
      ftc.performLevelConsistencyChecks(tracker.getTypingInformation().informal());
    }
    
    for (ParseResult parse : tracker.getParses()) {
      typeCheck(parse, itc, ftc);
    }
  }
  
  public static void typeCheck(ParseResult parse, InformalTypeChecker itc, FormalTypeChecker ftc) throws RecognitionException {
    Main.logDebug("Typechecking " + parse.getFilePath());
    
    CommonTree t = (CommonTree)parse.getParse().getTree(); //Get input tree
    CommonTreeNodeStream nodes = new CommonTreeNodeStream(t);  //Get stream of nodes from tree
    nodes.setTokenStream(parse.getTokens());

    walker.initialise(nodes, itc, ftc, parse.getFile()); //Reset walker, provide inputs

    walker.prog();  //Walk    
  }
  
}
