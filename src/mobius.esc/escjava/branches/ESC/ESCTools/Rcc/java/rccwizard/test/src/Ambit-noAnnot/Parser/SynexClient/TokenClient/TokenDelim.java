// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.SynexClient.TokenClient;

/** A single-character delimiter token */
/* Automatically changes a "special" character to a "delimiter" character */

import Parser.SynexClient.ScannerOne;
import Parser.Synex.Scanner.Token;

public class TokenDelim extends Token {

  public char ch; // read only

  public TokenDelim(char ch, ScannerOne scanner) {
    super();
    this.ch = ch;
    scanner.addDelimiter(ch);
  }

  public TokenDelim(char ch) {
    super();
    this.ch = ch;
  }

  public boolean equal(Token token) {
    if (token instanceof TokenDelim) {
      return (ch == ((TokenDelim)token).ch);
    } else {
      return false;
    }
  }

  public boolean match(Token token) {
    return (token instanceof TokenDelim);
  }

  public String toString() {
    return String.valueOf(ch);
  }

}
