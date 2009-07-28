// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeRoute extends CodeTerm {
// An routing capability.

  public CodeTerm segment1Code;
  public CodeTerm segment2Code;

  public CodeRoute(CodeTerm segment1Code, CodeTerm segment2Code, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.segment1Code = segment1Code;
    this.segment2Code = segment2Code;
  }
  
  public Result exec(Agent agent, Env env) throws ExecException {
    Result segment1 = segment1Code.exec(agent, env);
    Result segment2 = segment2Code.exec(agent, env);
    if ((!(segment1 instanceof Route)) || (!(segment2 instanceof Route))) { 
      throw new ExecException("Route expected.", this); 
    }
    return ((Route)segment1).append((Route)segment2);
  }
  
  public String toString() {
    return segment1Code.toString() + " & " + segment2Code.toString();
  }

}
