// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Parser;

/** The outcome of parsing. Any outcome must be a subclass of this. */

import Parser.Synex.Scanner.Location;

public class OutcomeLocated extends Outcome {

  public Location begLocation;
  public Location endLocation;

  public OutcomeLocated(Location begLocation, Location endLocation) {
    super();
    this.begLocation = begLocation;
    this.endLocation = endLocation;
  }

}
