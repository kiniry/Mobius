// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Grammar;

/** A sequential choice between grammars, with backtracking.  */
     
import Parser.Synex.Grammar.Grammar;
import Parser.Synex.Parser.Parser;
import Parser.Synex.Parser.ParseFailure;
import Parser.Synex.Parser.Outcome;
import Parser.Synex.Scanner.Token;
import Parser.Synex.SynexException;

public class Choice extends Grammar {

  GrammarList choices;

  public Choice(GrammarList choices) {
    this.choices = choices;
  }

  public Outcome accept(Parser parser) throws SynexException {
    Outcome outcome;
    GrammarList list = choices;
    while (list != null) {
      int scanPoint = parser.scanner.getScanPoint();
      outcome = list.first.accept(parser);
      if ((outcome == null) || !(outcome instanceof ParseFailure)) { return outcome; }
      if (parser.scanner.getScanPoint() != scanPoint) { return outcome; }
      list = list.next;
    }
    return new ParseFailure(parser.scanner.getLocation(), "Syntax Error");
  }

}
