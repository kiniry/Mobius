// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import java.util.Random;
import Parser.Synex.Scanner.Location;

public class CodeParallel extends CodeProc {
// The code that creates two parallel agents.
// Agent "P | P".

  private static Random rand = new Random();

  public CodeProc sequel1; // The code for the capability.
  public CodeProc sequel2; // The code to run afterwards.

  public CodeParallel(CodeProc sequel1, CodeProc sequel2, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.sequel1 = sequel1;
    this.sequel2 = sequel2;
  }
  
  public void exec(Agent agent, Env env) throws ExecException {
    CodeProc cont1; CodeProc cont2;
    if (rand.nextInt()%2 == 0) {
      cont1 = sequel1; cont2 = sequel2;
    } else {
      cont1 = sequel2; cont2 = sequel1;
    }
    agent.spawnAgent(cont1, env); // atomically in the same ambient
    agent.currentSequel = cont2;
    cont2.exec(agent, env);
  }
  
  public String toString() {
    return "(" + sequel1.toString() + "|" + sequel2.toString() + ")";
  }

}
