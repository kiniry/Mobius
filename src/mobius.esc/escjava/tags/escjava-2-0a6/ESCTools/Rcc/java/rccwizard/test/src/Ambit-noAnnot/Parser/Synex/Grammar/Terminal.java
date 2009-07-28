// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Grammar;

/** A given terminal symbol.  */
     
import Parser.Synex.Grammar.Grammar;
import Parser.Synex.Parser.Parser;
import Parser.Synex.Parser.ParseFailure;
import Parser.Synex.Parser.ParseSuccess;
import Parser.Synex.Parser.Outcome;
import Parser.Synex.Scanner.Token;
import Parser.Synex.Scanner.ScanFailureException;
import Parser.Synex.SynexException;

public class Terminal extends Grammar {

  Token terminalToken;

  public Terminal(Token terminalToken) {
    this.terminalToken = terminalToken;
  }

  public Outcome accept(Parser parser) throws ScanFailureException {
    boolean have;
    have = parser.scanner.haveToken(terminalToken);
    if (have) { 
      return ParseSuccess.parseSuccess;
    } else {
      return 
        new ParseFailure(parser.scanner.getLocation(), 
        "Syntax Error, expecting: '" + terminalToken.toString() + "\'");
    }
  }

}
