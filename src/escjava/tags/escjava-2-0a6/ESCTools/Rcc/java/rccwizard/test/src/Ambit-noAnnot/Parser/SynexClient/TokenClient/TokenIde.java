// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.SynexClient.TokenClient;

/** An indentifier (non-keyword) token */

import Parser.Synex.Scanner.Token;

public class TokenIde extends Token {

  public String ide; // read only

  public TokenIde(String ide) {
    super();
    this.ide = ide;
  }

  public boolean equal(Token token) {
    if (token instanceof TokenIde) {
      return ide.equals(((TokenIde)token).ide);
    } else {
      return false;
    }
  }

  public boolean match(Token token) {
    return (token instanceof TokenIde);
  }

  public String toString() {
    return ide;
  }
  
}
