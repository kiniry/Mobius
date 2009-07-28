// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Grammar;

/**  */

import Parser.Synex.Grammar.Grammar;
import Parser.Synex.Parser.Parser;
import Parser.Synex.Parser.ParseFailure;
import Parser.Synex.Parser.ParseSuccess;
import Parser.Synex.Parser.Outcome;
import Parser.Synex.Scanner.Token;
import Parser.Synex.SynexException;

public class Store extends Grammar {

  int displacement;
  Grammar gram;

  public Store(int displacement, Grammar gram) {
    this.displacement = displacement;
    this.gram = gram;
  }

  public Outcome accept(Parser parser) throws SynexException {
    Outcome outcome = gram.accept(parser);
    if ((outcome != null) && (outcome instanceof ParseFailure)) {
      return outcome;
    } else {
      if ((displacement < 0) || (displacement >= parser.currentInfo().frameSize)) {
        throw new BadGrammarException(
          "Index out of range in production '" + parser.currentInfo().productionName 
          + "', storing: " + Integer.toString(displacement));
      }
      if (parser.stack[parser.stackTop-displacement] != null) {
        throw new BadGrammarException(
          "Double assignment in production '" + parser.currentInfo().productionName 
          + "', storing: " + Integer.toString(displacement));
      }
      parser.stack[parser.stackTop-displacement] = outcome;
      return ParseSuccess.parseSuccess;
    }
  }

}
