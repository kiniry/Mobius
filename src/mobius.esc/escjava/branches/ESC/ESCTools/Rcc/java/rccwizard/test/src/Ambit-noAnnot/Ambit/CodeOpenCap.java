// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeOpenCap extends CodeTerm {
// An exit capability.

  public CodeTerm nameCode; // The code producing the name of the openCap.

  public CodeOpenCap(CodeTerm nameCode, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.nameCode = nameCode;
  }
  
  public Result exec(Agent agent, Env env) throws ExecException {
    Result name = nameCode.exec(agent, env);
    if (!(name instanceof Name)) { throw new ExecException("Name expected.", this); }
    return new Route(((Name)name).getOpenCap(), null);
  }
  
  public String toString() {
    return "open " + nameCode.toString();
  }

}
