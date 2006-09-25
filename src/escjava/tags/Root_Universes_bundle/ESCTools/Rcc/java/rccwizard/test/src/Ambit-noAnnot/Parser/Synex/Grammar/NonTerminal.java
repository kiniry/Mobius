// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Grammar;

/** A non-terminal grammar. Parsing a non-terminal is the
     same as setting-up a new stack frame and then parsing the associated 
     description; the returned Trees are the same. At the end, the new
     stack frame is cleared and popped. Parsing fails if parsing the 
     associated description fails.  */

import Parser.Synex.Grammar.Grammar;
import Parser.Synex.Grammar.ProductionInfo;
import Parser.Synex.Parser.Parser;
import Parser.Synex.Parser.ParseFailure;
import Parser.Synex.Parser.Outcome;
import Parser.Synex.Parser.Action;
import Parser.Synex.Scanner.Token;
import Parser.Synex.Scanner.ScanFailureException;
import Parser.Synex.SynexException;
import Parser.Synex.Scanner.Location;

public class NonTerminal extends GrammarNonTerminal {

  ProductionInfo info;
  Grammar gram;
  Action action;

  public NonTerminal() {
    super();
  }
  
  public void production(String productionName, Action action, int frameSize, int argsNo, Grammar gram) {
    /** productionName is just for error reporting */
    this.info = new ProductionInfo(productionName, 
                                    Math.max(0, Math.max(argsNo, frameSize)), Math.max(0, argsNo));
    this.gram = gram;  
    this.action = action;
  }
  
  public Outcome accept(Parser parser) throws SynexException {
    return acceptWithArgs(parser, null);
  }

  public Outcome acceptWithArgs(Parser parser, Args args) throws SynexException {
    Outcome outcome;
    parser.pushStack(info, args);
    try {
      Location begLocation = parser.scanner.getLocation();
      outcome = gram.accept(parser);
      Location endLocation = parser.scanner.getLocation();
      if ((outcome == null) || !(outcome instanceof ParseFailure)) {
        outcome = action.exec(parser, outcome, begLocation, endLocation);
      }
    } finally { parser.popStack(); }
    return outcome;
  }

}
