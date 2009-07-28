// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeAmbient extends CodeProc {
// The code that makes an agent create a new ambient.
// Agent "n[P]".

  public boolean marked; // Marked for top-level interaction.
  public CodeTerm ambientNameCode; // The code producing the name of the ambient.
  public CodeProc sequel; // The code to be run inside the new ambient.

  public CodeAmbient(boolean marked, CodeTerm ambientNameCode, CodeProc sequel, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.marked = marked;
    this.ambientNameCode = ambientNameCode;
    this.sequel = sequel;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
  // Add a new sub-ambient to the current ambient. Continue execution there.
  // P --> Q  ==>  n[P] --> n[Q]
    Result name = ambientNameCode.exec(agent, env);
    if (!(name instanceof Name)) { throw new ExecException("Name expected.", this); }
    Name ambientName = (Name)name;  
    agent.spawnAmbient(ambientName, env, marked);
    agent.currentSequel = sequel;
    sequel.exec(agent, env);
  }
  
  public String toString() {
    String mark = "";
    if (marked) { mark = "@"; }
    return mark + ambientNameCode.toString() + "[" + sequel.toString() + "]";
  }
  
}
