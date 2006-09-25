// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import java.lang.Thread;
import java.awt.TextArea;

public class Agent extends Thread {
// An agent.
// Every agent is single-threaded (except for printing threads); 
// therefore no methods here are synchronized, except when forking
// a concurrent agent in the same ambient (atomically).

  private Ambient ambient; // the current ambient of the agent
  private CodeProc code; // The code run by this agent.
  private Env initEnv; // The initial environment for running the code.
  private String messageBuffer; // for rendezvous -- later
  private Console console;

  public CodeProc currentSequel; // The code still to be executed, for printing.

  public Agent(Ambient ambient, CodeProc code, Env initEnv, Console console) {
  // Constructor.
    this.ambient = ambient;
    this.code = code;
    this.currentSequel = code;
    this.initEnv = initEnv;
    this.console = console;
  }
      
  public synchronized void doNotifyAll() {
    notifyAll();
  }
  
  public synchronized Ambient waitForParent() {
  // Get the parent ambient of this agent (blocks on null parent).
    while (ambient == null){
      try {wait();} catch (InterruptedException ex) {}
    }
    return ambient;
  }

  public void setAmbient(Ambient ambient) {
    this.ambient = ambient;
  }
  
  public Console getConsole() {
    return console;
  }
  
  public Agent spawnAgent(CodeProc code, Env initEnv) {
    // Create a new agent in the same ambient (atomically) as the current agent.
    // Return the new agent.
    Agent newAgent;
    do {
      newAgent = waitForParent().spawnAgent(this, code, initEnv);
    } while (newAgent == null);
    return newAgent;
  }
  
  public void spawnAmbient(Name name, Env initEnv, boolean marked) {
    // Create a new ambient in the same ambient (atomically) as the current agent.
    // Use the current agent to run the new ambient.
    boolean spawned;
    do {
      spawned = waitForParent().spawnAmbient(this, name, initEnv, marked);
    } while (!spawned);
  }

  public void moveOut(OutCap cap) throws AmbitException {
    boolean done;
    do {
      done = waitForParent().moveOut(this, cap);
    } while (!done);
  }
  
  public void moveIn(InCap cap) throws AmbitException {
    boolean done;
    do {
      done = waitForParent().moveIn(this, cap);
    } while (!done);
  }
    
  public void open(OpenCap cap) throws AmbitException {
    boolean done;
    do {
      done = waitForParent().open(this, cap);
    } while (!done);
  }
  
  public Result ask() throws AmbitException {
    Result result;
    do {
      result = waitForParent().ask(this);
    } while (result == null);
    return result;
  }
  
  public void say(Result result) throws AmbitException {
    boolean done;
    do {
      done = waitForParent().say(this, result);
    } while (!done);
  }

  public void run() {
    try {
      code.exec(this, initEnv);
    } catch (ExecException e) {
          scream(e.getMessage() + "\n");
          completed();
        } catch (java.lang.Exception ex) {
          scream("Java exception: " + ex.getMessage() + "\n");
          completed();
//    ex.printStackTrace();
    }
  }
  
  public void waitSeconds(double secs) {
    try {
      sleep(new Double(secs*1000.0).longValue());
    } catch (InterruptedException ex) {}
  }
  
  public void completed() {
    ambient.disownAgent(this);
  }
    
  public void scream(String screamMsg) {
    long now = System.currentTimeMillis();
    if (screamMsg.equals("")) { screamMsg = console.getState(); }
        console.appendOutput(ambient.getName() + "'s agent: " + screamMsg
          //-- + "      @" + Long.toString(now) 
          + "\n");
  }
      
  public String toString() {
    String string = "";
    if (currentSequel != null) { string = currentSequel.toString(); }
    return string;
  }
  
}
