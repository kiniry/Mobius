// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeProcIde extends CodeProc {
// The code that evaluates a process indentifier.

  public String ide; // The print-name of the identifier.
  
  public CodeProcIde(String ide, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.ide = ide;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
    Result result = null;
    try {
      result = env.fetch(ide);
    } catch (AmbitException ex) { throw new ExecException(ex.getMessage(), this); }
    if (!(result instanceof ProcClosure)) { throw new ExecException("Process expected", this); }
    ProcClosure closure = (ProcClosure)result;
    agent.currentSequel = closure.body;
    closure.body.exec(agent, closure.env);
    
  }
  
  public String toString() {
    return ide;
  }
  
}
