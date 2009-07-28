// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.SynexClient.TokenClient;

/** A quoted string token */

import Parser.SynexClient.ScannerOne;
import Parser.Synex.Scanner.Token;

public class TokenString extends Token {

  public String str; // read only

  public TokenString(String str) {
    super();
    this.str = str;
  }

  public boolean equal(Token token) {
    if (token instanceof TokenString) {
      return str.equals(((TokenString)token).str);
    } else {
      return false;
    }
  }

  public boolean match(Token token) {
    return (token instanceof TokenString);
  }

  public String toString() {
    return "\"" + ScannerOne.encodeString(str) + "\"";
  }
  
}
