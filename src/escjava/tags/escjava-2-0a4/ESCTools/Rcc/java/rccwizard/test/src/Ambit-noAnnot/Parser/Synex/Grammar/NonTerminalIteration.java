// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Grammar;

/** A sequential choice between grammars, with backtracking.  */
     
import Parser.Synex.Grammar.Grammar;
import Parser.Synex.Grammar.NonTerminal;
import Parser.Synex.Grammar.GrammarNonTerminal;
import Parser.Synex.Parser.Parser;
import Parser.Synex.Parser.ParseFailure;
import Parser.Synex.Parser.IterationAction;
import Parser.Synex.Parser.Outcome;
import Parser.Synex.Scanner.Token;
import Parser.Synex.SynexException;
import Parser.Synex.Scanner.Location;

public class NonTerminalIteration extends GrammarNonTerminal {

  ProductionInfo info;
  GrammarNonTerminal baseGram; 
  Grammar iterGram;
  IterationAction action;

  public NonTerminalIteration() {
    super();
  }
  
  public void production(String productionName, IterationAction action, int frameSize, GrammarNonTerminal baseGram, Grammar iterGram) {
    /** productionName is just for error reporting */
    this.info = new ProductionInfo(productionName, Math.max(0, frameSize), 0); // no argsNo
    this.baseGram = baseGram;  
    this.iterGram = iterGram;  
    this.action = action;
  }

  public Outcome accept(Parser parser) throws SynexException {
    Outcome outcome;
    Outcome accumulator = baseGram.accept(parser);
    if ((accumulator != null) && (accumulator instanceof ParseFailure)) { return accumulator; }
    while (true) {
      int scanPoint = parser.scanner.getScanPoint();
      parser.pushStack(info, null); // no args
      try {
        Location begLocation = parser.scanner.getLocation();
        outcome = iterGram.accept(parser);
        Location endLocation = parser.scanner.getLocation();
        if ((outcome != null) && (outcome instanceof ParseFailure)) { 
          if (parser.scanner.getScanPoint() != scanPoint) {
            accumulator = outcome;
          }
          break;
        }
        accumulator = action.exec(parser, accumulator, outcome, begLocation, endLocation);
      } finally { parser.popStack(); }
    }
    return accumulator;
  }

}
