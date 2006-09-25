// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeImplode extends CodeProc {
// The code that makes an agent's ambient implode.
// Agent "#".

  public CodeImplode(Location begLocation, Location endLocation) { 
  // Constructor.
    super(begLocation, endLocation);
  }
   
  public void exec(Agent agent, Env env) throws ExecException {
  // Implode the agent's ambient.
    agent.currentSequel = null;
    agent.waitForParent().implode();
  }
  
  public String toString() {
    return "#";
  }
  
}
