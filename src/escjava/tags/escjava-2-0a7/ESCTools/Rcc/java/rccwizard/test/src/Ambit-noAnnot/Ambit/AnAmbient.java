// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

public interface AnAmbient {

// Structure

  public Name getName();
  // The current name of this ambient.
  
  public Env getInitEnv();
  // Get initEnv, the environment at the time this ambient was created (never changes).

  public void startAgent(CodeProc code, Env env) throws AmbitException;
  // Start a new agent in this ambient. The agent runs code with initial environment env.
  // For a "fresh" agent, env should be set to initEnv.
  // For a "continuing" agent (e.g. one forked off by a par), env could be longer than initEnv.

// Movement

  public boolean moveOut(Agent agent, OutCap parentCap) throws AmbitException;
  // Move this ambient outside the parent (it becomes a sibling of the parent).
  // Requires an output capability to exit the parent.
  // Blocks until a parent's parent exists, and until a parent matches the capability.

  public boolean moveIn(Agent agent, InCap receiverCap) throws AmbitException;
  // Move this ambient inside a sibling ambient (it becomes a child of the sibling).
  // Requires an input capability to enter the sibling.
  // Blocks until a parent exists, and until a sibling matches the capability.

  public void become(Name newName) throws AmbitException;
  // Rename this ambient.
  // Blocks until a parent exists (to avoid races with other operations).

  public void implode() throws AmbitException;
  // The current ambient goes poof. (It is removed from its parent.)
  // Blocks until a parent exists.

// Communication
  
  public boolean say(Agent agent, Result result) throws AmbitException;
  // Outputs a value into the ambient's ether.
  // Asynchronous (non-blocking).

  public Result ask(Agent agent) throws AmbitException;
  // Input a value from the ambient's ether.
  // Blocks until it can match an output.

// Utility

  public void scream(String screamMsg);
  // Scream a message from this ambient to a global console.

  public String toString();
  // Display the current state of the ambient.
  // If the ambient is changing, it may display an inconsistent configuration.

}
