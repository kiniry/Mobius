// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Scanner;

import Parser.Synex.SynexException;

public class ScanFailureException extends SynexException {

  public ScanFailureException(String msg) {
    super(msg);
  }

}
