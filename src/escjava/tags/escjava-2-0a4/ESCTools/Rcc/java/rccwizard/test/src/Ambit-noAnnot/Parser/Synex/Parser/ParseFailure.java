// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Parser;

/** An outcome representing parsing failure. */

import Parser.Synex.Parser.OutcomeLocated;
import Parser.Synex.Scanner.Location;

public class ParseFailure extends OutcomeLocated {

  public String msg;

  public ParseFailure(Location location, String msg) {
    super(location, location);
    this.msg = msg;
  }

}
