// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeSay extends CodeProc {
// The code that creates a new name.
// Agent "say a".

  public CodeTerm output; // The code to produce the output.
  public CodeProc sequel; // The code to run afterwards.

  public CodeSay(CodeTerm output, CodeProc sequel, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.output = output;
    this.sequel = sequel;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
    Result result = output.exec(agent, env);
    try {
      agent.say(result);
    } catch (AmbitException ex) { throw new ExecException(ex.getMessage(), this); }
    agent.currentSequel = sequel;
    sequel.exec(agent, env);
  }
  
  public String toString() {
    return "say " + output.toString() + "." + sequel.toString();
  }
  
}
