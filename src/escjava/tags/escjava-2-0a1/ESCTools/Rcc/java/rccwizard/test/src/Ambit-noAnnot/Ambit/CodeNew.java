// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeNew extends CodeProc {
// The code that creates a new name.
// Agent "(nu n)P".

  public String printName; // The print-name of the new name.
  public CodeProc sequel; // The code to run afterwards.

  public CodeNew(String printName, CodeProc sequel, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.printName = printName;
    this.sequel = sequel;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
    agent.currentSequel = sequel;
    sequel.exec(agent, new EnvCons(printName, new Name(printName), env));
  }
  
  public String toString() {
    return "new " + printName + "." + sequel.toString();
  }
  
}
