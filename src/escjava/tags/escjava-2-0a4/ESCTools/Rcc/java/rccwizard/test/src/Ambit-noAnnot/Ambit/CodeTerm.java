// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;
import Parser.Synex.Parser.OutcomeLocated;

public abstract class CodeTerm extends OutcomeLocated {
// Code run by an agent to evaluate a term.

  public CodeTerm(Location begLocation, Location endLocation) {
    super(begLocation, endLocation);
  }
  
  public abstract Result exec(Agent agent, Env env) throws ExecException;
  // The execution method for the code.
  
  public abstract String toString();
  // Print the code, for debugging.
  
}
