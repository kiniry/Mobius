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

public class Apply extends Grammar {

  NonTerminal nonTerminal;
  Args args;

  public Apply(NonTerminal nonTerminal, Args args) {
    this.nonTerminal = nonTerminal;
    this.args = args;
  }

  public Outcome accept(Parser parser) throws SynexException {
    return nonTerminal.acceptWithArgs(parser, args);
  }

}
