// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.SynexClient.TokenClient;

/** A quoted character token */

import Parser.SynexClient.ScannerOne;
import Parser.Synex.Scanner.Token;

public class TokenChar extends Token {

  public char ch; // read only

  public TokenChar(char ch) {
    super();
    this.ch = ch;
  }
  
  public boolean equal(Token token) {
    if (token instanceof TokenChar) {
      return (ch == ((TokenChar)token).ch);
    } else {
      return false;
    }
  }

  public boolean match(Token token) {
    return (token instanceof TokenChar);
  }

  public String toString() {
    return "\'" + ScannerOne.encodeChar(ch) + "\'";
  }

}
