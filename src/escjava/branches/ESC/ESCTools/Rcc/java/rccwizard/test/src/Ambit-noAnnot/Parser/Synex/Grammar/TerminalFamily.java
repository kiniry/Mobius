// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Grammar;

/** A family of terminal symbols. E.g. integer, string, identifier ...  */
     
import Parser.Synex.Grammar.Grammar;
import Parser.Synex.Parser.Parser;
import Parser.Synex.Parser.ParseFailure;
import Parser.Synex.Parser.ParseSuccess;
import Parser.Synex.Parser.Outcome;
import Parser.Synex.Scanner.Token;
import Parser.Synex.Scanner.ScanFailureException;
import Parser.Synex.SynexException;

public class TerminalFamily extends Grammar {

  Token terminalTokenExample;

  public TerminalFamily(Token terminalTokenExample) {
    /** the parameter is an "example" of the kind of token we want to match. */
    this.terminalTokenExample = terminalTokenExample;
  }

  public Outcome accept(Parser parser) throws ScanFailureException {
    Outcome outcome;
    outcome = parser.scanner.matchToken(terminalTokenExample);
    if (outcome == null) { 
      return 
        new ParseFailure(parser.scanner.getLocation(), 
              "Syntax Error, expecting a different terminal");
    } else {
      return outcome;
    }
  }

}
