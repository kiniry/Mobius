// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Grammar;

import Parser.Synex.SynexException;

public class BadGrammarException extends SynexException {

  public BadGrammarException(String msg) {
    super(msg);
  }

}
