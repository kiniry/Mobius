// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.SynexClient.TokenClient;

/** A keyword token */

import Parser.SynexClient.ScannerOne;
import Parser.Synex.Scanner.Token;

public class TokenKey extends Token {

  public String key; // read only

  public TokenKey(String key, ScannerOne scanner) {
    super();
    this.key = key;
    scanner.addKeyword(key);
  }

  public TokenKey(String key) {
    super();
    this.key = key;
  }

  public boolean equal(Token token) {
    if (token instanceof TokenKey) {
      return key.equals(((TokenKey)token).key);
    } else {
      return false;
    }
  }

  public boolean match(Token token) {
    return (token instanceof TokenKey);
  }

  public String toString() {
    return key;
  }
  
}
