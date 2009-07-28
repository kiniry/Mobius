// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;
import Parser.Synex.Parser.OutcomeLocated;

public class CodeLet extends CodeProc {

  public String ide; // The defined proc ide.
  public IdeList params; // The defined proc parameters.
  public CodeProc proc; // The defined proc body.
  public CodeProc sequel; // The scope of the definition.

  public CodeLet(String ide, IdeList params, CodeProc proc, CodeProc sequel, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.ide = ide;
    this.params = params;
    this.proc = proc;
    this.sequel = sequel;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
    Env letEnv = LetClosure.ConsLet(ide, params, proc, env);
    agent.currentSequel = sequel;
    sequel.exec(agent, letEnv);
  }

  public String toString() {
    String str = "let " + ide + "(";
    if (params != null) { str += params.toString(); }
    str += ") = " + proc.toString() + "; " + sequel.toString();
    return str;
  }

}
