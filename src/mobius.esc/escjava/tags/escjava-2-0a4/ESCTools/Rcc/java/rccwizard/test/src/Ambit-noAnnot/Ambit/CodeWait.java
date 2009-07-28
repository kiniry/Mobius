// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeWait extends CodeProc {

  public CodeTerm timeCode;
  public CodeProc sequel; // The code to run afterwards.

  public CodeWait(CodeTerm timeCode, CodeProc sequel, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.timeCode = timeCode;
    this.sequel = sequel;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
    Result time = timeCode.exec(agent, env);
    if (!(time instanceof Real)) { throw new ExecException("Real expected.", this); }
    agent.currentSequel = sequel;
    agent.waitSeconds(((Real)time).real);
    sequel.exec(agent, env);
  }
  
  public String toString() {
    return "wait " + timeCode.toString() + "." + sequel.toString();
  }
  
}
