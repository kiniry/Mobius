// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;
import Parser.Synex.Parser.OutcomeLocated;

public abstract class CodeProc extends OutcomeLocated {
// Code run by an agent to evaluate a process.

  public CodeProc(Location begLocation, Location endLocation) {
    super(begLocation, endLocation);
  }
  
  public abstract void exec(Agent agent, Env env) throws ExecException;
  // The execution method for the code.
  
  public abstract String toString();
  // Print the code, for debugging.
  
}
