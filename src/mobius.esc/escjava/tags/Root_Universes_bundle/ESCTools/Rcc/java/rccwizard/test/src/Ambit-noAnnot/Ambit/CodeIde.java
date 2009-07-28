// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeIde extends CodeTerm {
// The code that evaluates an indentifier.
// Agent "x".

  public String ide; // The print-name of the identifier.
  
  public CodeIde(String ide, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.ide = ide;
  }
  
  public Result exec(Agent agent, Env env) throws ExecException {
    try {
      return env.fetch(ide);
    } catch (AmbitException ex) { throw new ExecException(ex.getMessage(), this); }
  }
  
  public String toString() {
    return ide;
  }
  
}
