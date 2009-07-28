// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;
import Parser.Synex.Parser.OutcomeLocated;

public class CodeTopFocus extends OutcomeLocated {

  public String ide; // The ide.

  public CodeTopFocus(String ide, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.ide = ide;
  }
  
  public String toString() {
    return "at " + ide;
  }

}
