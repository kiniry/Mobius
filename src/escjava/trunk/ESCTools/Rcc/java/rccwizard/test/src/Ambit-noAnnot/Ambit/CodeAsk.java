// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeAsk extends CodeProc {
// The code that creates a new name.
// Agent "ask x.P".

  public String printName; // The print-name of the new name.
  public CodeProc sequel; // The code to run afterwards.

  public CodeAsk(String printName, CodeProc sequel, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.printName = printName;
    this.sequel = sequel;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
    Result result = null;
    try {
      result = agent.ask();
    } catch (AmbitException ex) { throw new ExecException(ex.getMessage(), this); }
    agent.currentSequel = sequel;
    sequel.exec(agent, new EnvCons(printName, result, env));
  }
  
  public String toString() {
    return "ask " + printName + "." + sequel.toString();
  }
  
}
