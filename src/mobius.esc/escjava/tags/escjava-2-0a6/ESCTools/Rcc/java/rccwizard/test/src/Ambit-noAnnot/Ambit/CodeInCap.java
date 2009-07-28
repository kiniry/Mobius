// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeInCap extends CodeTerm {
// An enter capability.

  public CodeTerm nameCode; // The code producing the name of the inCap.

  public CodeInCap(CodeTerm nameCode, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.nameCode = nameCode;
  }
  
  public Result exec(Agent agent, Env env) throws ExecException {
    Result name = nameCode.exec(agent, env);
    if (!(name instanceof Name)) { throw new ExecException("Name expected.", this); }
    return new Route(((Name)name).getInCap(), null);
  }

  public String toString() {
    return "in " + nameCode.toString();
  }
  
}
