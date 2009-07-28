// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Grammar;

/** The grammar for parsing. */

import Parser.Synex.Parser.Outcome;
import Parser.Synex.Parser.Parser;
import Parser.Synex.SynexException;

public abstract class GrammarNonTerminal extends Grammar {

  public GrammarNonTerminal() {}
  
  public abstract Outcome accept(Parser parser) throws SynexException;

}
