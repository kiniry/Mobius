// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Parser.OutcomeLocated;

public class ExecException extends Exception {

  public ExecException(String msg, OutcomeLocated culprit) {
    super("Execution exception: " + msg + "\n" + 
      culprit.begLocation.streamLineCharRangeMsg(culprit.endLocation));
  }

}
