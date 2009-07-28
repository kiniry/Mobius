// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;
import Parser.Synex.Parser.OutcomeLocated;

public class CodeLetExpansion extends CodeProc {

  public String ide; // The defined proc ide.
  public TermList args; // The defined proc arguments.
  public CodeTerm route; // The route to follow to find the definition of ide.

  public CodeLetExpansion(String ide, TermList args, CodeTerm route, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.ide = ide;
    this.args = args;
    this.route = route;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
    if (route != null) {
      // --- evaluate and follow route to find the appropriate env
      // --- let declarations should set up an externally visible env
      //     the so that definitions can be found.
    }
    try {
      Result ideVal = env.fetch(ide);
      if (ideVal instanceof LetClosure) {
        LetClosure closure = (LetClosure) ideVal;
        Env extnEnv = env;
        IdeList parameters = closure.params;
        TermList arguments = args;
        while ((!(parameters == null)) && (!(arguments == null))) {
          Result arg = arguments.term.exec(agent, env);
          extnEnv = new EnvCons(parameters.ide, arg, extnEnv);
          parameters = parameters.next;
          arguments = arguments.next;
        }
        if ((!(parameters == null)) || (!(arguments == null))) {
          throw new ExecException("Different number of arguments and parameters for " + ide, this); 
        }
        closure.body.exec(agent, extnEnv);
      } else { throw new ExecException("identifier " + ide + " not bound to a 'let' definition", this); }
    } catch (AmbitException ex) { throw new ExecException(ex.getMessage(), this); }
  }

  public String toString() {
    String str = ide + "(";
    if (args != null) { str += args.toString(); }
    str += ")";
    if (route != null) {str += " at " + route.toString(); }
    return str;
  }

}
