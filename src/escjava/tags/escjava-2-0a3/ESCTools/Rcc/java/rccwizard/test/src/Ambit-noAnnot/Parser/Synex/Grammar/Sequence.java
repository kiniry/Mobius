// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Grammar;

/** A sequential choice between grammars, with backtracking.  */
     
import Parser.Synex.Grammar.Grammar;
import Parser.Synex.Parser.Parser;
import Parser.Synex.Parser.ParseFailure;
import Parser.Synex.Parser.ParseSuccess;
import Parser.Synex.Parser.Outcome;
import Parser.Synex.Scanner.Token;
import Parser.Synex.SynexException;

public class Sequence extends Grammar {

  GrammarList items;

  public Sequence(GrammarList items) {
    this.items = items;
  }

  public Outcome accept(Parser parser) throws SynexException {
    Outcome outcome;
    GrammarList list = items;
    while (list != null) {
      outcome = list.first.accept(parser);
      if ((outcome != null) && (outcome instanceof ParseFailure)) {
        return outcome;
      }
      list = list.next;
    }
    return ParseSuccess.parseSuccess;
  }

}
