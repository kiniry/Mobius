// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeStay extends CodeTerm {
// An routing capability.

  public CodeStay(Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
  }
  
  public Result exec(Agent agent, Env env) throws ExecException {
    return new Route(new Stay(), null);
  }
  
  public String toString() {
    return "stay";
  }

}
