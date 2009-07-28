// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeDo extends CodeProc {
// The code that makes an agent enter an ambient.

  public CodeTerm routeCode; // The code for the capability.
  public CodeProc sequel; // The code to run afterwards.

  public CodeDo(CodeTerm routeCode, CodeProc sequel, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.routeCode = routeCode;
    this.sequel = sequel;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
    Result routeResult = routeCode.exec(agent, env);
    if (!(routeResult instanceof Route)) {throw new ExecException("Route expected.", this);}
    Route route = (Route)routeResult;
    while (route != null) {
      if (route.step instanceof InCap) {
        try {
          agent.moveIn((InCap)route.step);
        } catch (AmbitException ex) { throw new ExecException(ex.getMessage(), this); }
      } else if (route.step instanceof OutCap) {
        try {
          agent.moveOut((OutCap)route.step);
        } catch (AmbitException ex) { throw new ExecException(ex.getMessage(), this); }
      } else if (route.step instanceof OpenCap) {
        try {
          agent.open((OpenCap)route.step);
        } catch (AmbitException ex) { throw new ExecException(ex.getMessage(), this); }
      } else if (route.step instanceof Stay) {
      } else throw new ExecException("Capability expected.", this);
      route = route.next;
    }
    agent.currentSequel = sequel;
    sequel.exec(agent, env);
  }
  
  public String toString() {
    return "do " + routeCode.toString() + "." + sequel.toString();
  }

}
