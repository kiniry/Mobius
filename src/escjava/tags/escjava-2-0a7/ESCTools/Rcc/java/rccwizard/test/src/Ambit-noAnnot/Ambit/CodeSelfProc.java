// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;
import Parser.Synex.Parser.OutcomeLocated;

public class CodeSelfProc extends OutcomeLocated {
// Code run by an agent to evaluate a process.

  public CodeProc proc; // The code to run in the self ambient.

  public CodeSelfProc(CodeProc proc, Location begLocation, Location endLocation) {
    super(begLocation, endLocation);
    this.proc = proc;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
    agent.currentSequel = proc;
    proc.exec(agent, env);
  }
  
  public String toString() {
    return "I " + proc.toString();
  }
  
}
