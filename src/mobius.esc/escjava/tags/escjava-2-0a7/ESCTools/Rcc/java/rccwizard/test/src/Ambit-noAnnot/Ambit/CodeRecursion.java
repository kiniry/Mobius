// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeRecursion extends CodeProc {

  public String ideName; // The recursive process ide.
  public CodeProc sequel; // The recursive body.

  public CodeRecursion(String ideName, CodeProc sequel, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.ideName = ideName;
    this.sequel = sequel;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
    Env recEnv = ProcClosure.ConsRec(ideName, sequel, env);
    agent.currentSequel = sequel;
    sequel.exec(agent, recEnv);
  }
  
  public String toString() {
    return "rec " + ideName + "." + sequel.toString();
  }

}
