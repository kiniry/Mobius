// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.SynexClient.TokenClient;

/** A quoted character token */

import Parser.Synex.Scanner.Token;

public class TokenInt extends Token {

  public int n; // read only

  public TokenInt(int n) {
    super();
    this.n = n;
  }

  public boolean equal(Token token) {
    if (token instanceof TokenInt) {
      return (n == ((TokenInt)token).n);
    } else {
      return false;
    }
  }

  public boolean match(Token token) {
    return (token instanceof TokenInt);
  }

  public String toString() {
    return (n>=0) ? Integer.toString(n) : ("~" + Integer.toString(-n));
  }

}
