// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeStop extends CodeProc {
// The code that makes an agent stop.
// Agent "0".

  public CodeStop(Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
  // Stop the agent, which is the current thread.
  // "0 -/-> "
    agent.currentSequel = null;
    agent.completed();
  }
  
  public String toString() {
    return "-";
  }
  
}
