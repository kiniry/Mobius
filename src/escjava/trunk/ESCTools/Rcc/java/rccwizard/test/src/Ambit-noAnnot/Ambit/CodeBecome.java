// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeBecome extends CodeProc {
// The code that makes an agent change the name of its ambient.

  public CodeTerm nameCode; // The code for the new name.
  public CodeProc sequel; // The code to run afterwards.

  public CodeBecome(CodeTerm nameCode, CodeProc sequel, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.nameCode = nameCode;
    this.sequel = sequel;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
    Result newName = nameCode.exec(agent, env);
    if (newName instanceof Name) {
      try {
        agent.waitForParent().become((Name)newName);
      } catch (AmbitException ex) { throw new ExecException(ex.getMessage(), this); }
    } else throw new ExecException("Name expected.", this);
    agent.currentSequel = sequel;
    sequel.exec(agent, env);
  }
  
  public String toString() {
    return "be " + nameCode.toString() + "." + sequel.toString();
  }

}
