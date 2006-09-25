// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Scanner;

import Parser.Synex.Parser.Outcome;

public abstract class Token extends Outcome {

  int tokenBegPos, tokenEndPos;
      
  public Token() {
  }
  
  public abstract boolean equal(Token token);
  /** Are these two tokens equal? 
      E.g. is this a given delimiter token? */

  public abstract boolean match(Token token);
  /** Are these two the same king of tokens? 
      E.g. are these two integer tokens, but possibly with different 
      integers? */

}
