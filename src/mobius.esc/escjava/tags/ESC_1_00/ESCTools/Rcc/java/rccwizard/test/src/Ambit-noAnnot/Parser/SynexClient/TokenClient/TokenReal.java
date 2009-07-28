// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.SynexClient.TokenClient;

/** A quoted character token */

import Parser.Synex.Scanner.Token;

public class TokenReal extends Token {

  public double r; // read only

  public TokenReal(double r) {
    super();
    this.r = r;
  }

  public boolean equal(Token token) {
    if (token instanceof TokenReal) {
      return (r == ((TokenReal)token).r);
    } else {
      return false;
    }
  }

  public boolean match(Token token) {
    return (token instanceof TokenReal);
  }
  
  public String toString() {
    return (r>=0.0) ? Double.toString(r) : ("~" + Double.toString(-r));
  }

}
