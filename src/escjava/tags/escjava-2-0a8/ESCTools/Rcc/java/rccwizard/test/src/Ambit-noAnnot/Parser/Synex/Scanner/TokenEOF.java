// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Scanner;

/** A token to be returned to signal an end-of-file. (To be used 
    optionally, in case EOF is explicitly part of the grammar and not 
    simply ignored.) */
    
import Parser.Synex.Scanner.Token;

public class TokenEOF extends Token {

  public TokenEOF() {
  }

  public boolean equal(Token token) {
    return (token instanceof TokenEOF);
  }
  
  public boolean match(Token token) {
    return (token instanceof TokenEOF);
  }
  
  public String toString() {
    return "<EOF>";
  }

}
