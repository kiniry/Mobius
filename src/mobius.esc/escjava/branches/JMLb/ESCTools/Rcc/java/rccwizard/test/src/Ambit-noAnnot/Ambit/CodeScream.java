// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeScream extends CodeProc {
// The code that creates a new name.
// Agent "scream "help!". P".

  public String screamMsg; // The scream.
  public CodeProc sequel; // The code to run afterwards.

  public CodeScream(String screamMsg, CodeProc sequel, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.screamMsg = screamMsg;
    this.sequel = sequel;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
    agent.currentSequel = sequel;
    agent.scream(screamMsg);
    sequel.exec(agent, env);
  }
  
  public String toString() {
    return "\"" + screamMsg + "\"" + "." + sequel.toString(); // -- encode screamMsg
  }
  
}
