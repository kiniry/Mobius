// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import java.lang.Thread;
import java.util.Vector;
import java.util.Enumeration;
import java.awt.TextArea;

public class Ambient implements AnAmbient {
// An ambient.

  // === Instance Variables === //
  
    private Name name; // The current name of the ambient.
  private Ambient parent; // The ambient surrounding this, or null.
    final private Vector ownAmbients; // The set of active subambients.
    final private Vector ownAgents; // The set of agents in this ambient.
    final private Vector ownMessages;
    // For local I/O.
    final private Env initEnv; // Initial environment for this ambient.
  final private Console console; // Tracing, debugging, etc.

  // === Constructors === //
  
  public Ambient(Name name, Env initEnv, Console console) {
  // Create a new, detached, empty ambient.
    this.parent = null;
    this.name = name;
    this.ownAmbients = new Vector();
    this.ownAgents = new Vector();
    this.ownMessages = new Vector();
    this.initEnv = initEnv;
    this.console = console;
  }
 
  // === Handling agents === //
  
  public synchronized void startAgent(CodeProc code, Env env) {
    // Simplified version of spawnAgent
    scream("Starting agent " + code.toString()); // -- trace
    Agent agent = new Agent(this, code, env, console);
    ownAgents.addElement(agent);
    agent.start();
  }
 
  public synchronized Agent spawnAgent(Agent spawningAgent, CodeProc code, Env env) {
    // An agent spawns another agent in the same ambient
    if (!ownAgents.contains(spawningAgent)) {return null;} // arbitrates race
    scream("Spawning agent " + code.toString()); // -- trace
    Agent agent = new Agent(this, code, env, console);
    ownAgents.addElement(agent);
    agent.start();
    return agent;
  } 
  
  public synchronized void adoptAgent(Agent agent) {
  // This ambients adopts a running agent.
    agent.setAmbient(this);
    ownAgents.addElement(agent);
    agent.doNotifyAll();
  }
  
  public synchronized void disownAgent(Agent agent) {
  // Disown a running agent.
    ownAgents.removeElement(agent);
    agent.setAmbient(null);
  }
  
  public synchronized boolean spawnAmbient(Agent spawningAgent, Name name, Env env, boolean marked) {
    if (!ownAgents.contains(spawningAgent)) {return false;} // arbitrates race
    scream("Spawning ambient " + name.toString()); // -- trace
    Ambient subAmbient = new Ambient(name, env, console);
    if (marked) {console.markedAmbient(subAmbient); }
    ownAgents.removeElement(spawningAgent);
    subAmbient.adoptAgent(spawningAgent);
    subAmbient.insertInto(this);
    return true;
    // This is an optimization:
    // reuse the current agent instead of starting a new one in the new ambient.
  }
  
  // === Name, Parent, Children === //
  
  private synchronized void doNotifyAll() {
    notifyAll();
  }
  
  public synchronized Name getName() {
  // The name of this ambient.
    return name;
  }
  
  public Env getInitEnv() {
    return initEnv;
  }
  
  private synchronized void setParent(Ambient newParent) {
  // Set the parent of this ambient.
    parent = newParent;
  }
  
  private synchronized Ambient waitForParent() {
  // Get the parent of this ambient (blocks on null parent).
    while (parent == null){
      try {wait();} catch (InterruptedException ex) {}
    }
    return parent;
  }
  
    // === InsertChild === //
    
  public synchronized void insertInto(Ambient newParent) {
  // Insert this ambient into newParent and notify both.
    parent = newParent;
    newParent.insertChild(this);
    newParent.doNotifyAll(); // wake up siblings waiting for new child
    notifyAll(); // wake up agents waiting for a non-null parent
  }
  
  private synchronized void insertChild(Ambient ambient) {
    ownAmbients.addElement(ambient);
  }

// === Match ambient === //
    
  private Ambient findMatchingParent(OutCap outCap) {
      if ((parent != null) && getName().matches(outCap)) {
          return parent; 
    } else {
      return null;
    }
  }

  private Ambient findMatchingChild(Ambient subjectAmbient, Cap cap) {
    Enumeration enum = ownAmbients.elements();
    while (enum.hasMoreElements()) {
      Ambient ambient = (Ambient)enum.nextElement();
      if ((ambient != subjectAmbient) && (ambient.getName().matches(cap))) {
        return ambient;
      }
    }
    return null;
  }
  
  // === Moving out === //

  public boolean moveOut(Agent agent, OutCap parentCap) throws AmbitException {
  // Move this ambient above parent.
      
      if (!ownAgents.contains(agent)) 
        {return false;} // arbitrates race
    Ambient newParent = waitForParent().movingOut(this, parentCap);
    if (newParent != null) {
      insertInto(newParent);
      return true;
    } else {
      return false;
    }
  }
  
  private synchronized Ambient movingOut(Ambient ambient, OutCap outCap) {
    if (!ownAmbients.contains(ambient)) {return null;} // arbitrates race
    Ambient myParent = findMatchingParent(outCap);
    if (myParent != null) {
      ownAmbients.removeElement(ambient);
      ambient.setParent(null);
      notifyAll();
      ambient.scream("Moved out " + name.toString()); // -- trace
    } else { 
      try {wait();} catch (InterruptedException ex) {}
    }
    return myParent;
  } 
 
  // === Moving in === //
  
  public boolean moveIn(Agent agent, InCap receiverCap) throws AmbitException {
  // Move this ambient inside receivingAmbient; they are currently siblings.
      if (!ownAgents.contains(agent)) 
        {return false;} // arbitrates race
    Ambient newParent = waitForParent().movingIn(this, receiverCap);
    if (newParent != null) {
      insertInto(newParent);
      return true;
    } else {
      return false;
    }
  }
  
  private synchronized Ambient movingIn(Ambient ambient, InCap inCap) {
    if (!ownAmbients.contains(ambient)) {return null;} // arbitrates race
    Ambient myChild = findMatchingChild(ambient, inCap);
    if (myChild != null) {
      ownAmbients.removeElement(ambient);
      ambient.setParent(null);
      notifyAll();
      ambient.scream("Moved " + inCap.toString()); // -- trace
    } else { 
      try {wait();} catch (InterruptedException ex) {}
    }
    return myChild;
  }
  
  // === Opening === //

  public synchronized boolean open(Agent agent, OpenCap openCap) throws AmbitException {
    if (!ownAgents.contains(agent)) {return false;} // arbitrates race
    Ambient targetChild = findMatchingChild(this, openCap);
    if (targetChild != null) {
      ownAmbients.removeElement(targetChild);
      targetChild.setParent(null);
      targetChild.transplantNephews(this); // do all the notify
      scream("Opened " + openCap.toString()); // -- trace
      return true;
    } else { 
      try {wait();} catch (InterruptedException ex) {}
      return false;
    }
  }

  private synchronized void transplantNephews(Ambient parent) {
    Enumeration enumAmbients = ownAmbients.elements();
    while (enumAmbients.hasMoreElements()) {
      Ambient nephew = (Ambient)enumAmbients.nextElement();
      scream("Transplanting ambient " + nephew.getName().toString()); // -- trace
      ownAmbients.removeElement(nephew);
      nephew.setParent(parent);
      parent.insertChild(nephew);
      nephew.doNotifyAll();
    }
    Enumeration enumAgents = ownAgents.elements();
    while (enumAgents.hasMoreElements()) {
      Agent nephew = (Agent)enumAgents.nextElement();
      scream("Transplanting agent " + nephew.toString()); // -- trace
      disownAgent(nephew);
      parent.adoptAgent(nephew);
    }    
    Enumeration enumMessages = ownMessages.elements();
    while (enumMessages.hasMoreElements()) {
      Result message = (Result)enumMessages.nextElement();
      scream("Transplanting message " + message.toString()); // -- trace
      parent.addMessage(message);
    }
    parent.doNotifyAll();
    notifyAll();
  }  

  // === Becoming === //
  
  public void become(Name newName) throws AmbitException {
  // Rename this ambient; must lock parent to prevent races.
    while (!waitForParent().becoming(this, newName)) {}
  }
  
  private synchronized boolean becoming(Ambient ambient, Name newName) {
    if (!ownAmbients.contains(ambient)) {return false;} // arbitrates race
    ambient.setName(newName);
    notifyAll();
    return true;
  }
  
  private synchronized void setName(Name newName) {
    scream("Be " + newName.toString()); // -- trace
    name = newName;
    notifyAll();
  }

  // === Imploding === //

  public void implode() {
  // Ambient implosion.
    waitForParent().imploding(this);
    setParent(null);
    // -- kill all subthreads
    scream("Aagh!");
  }
      
  private synchronized void imploding(Ambient ambient) {
    ownAmbients.removeElement(ambient);
  }
    
  // === -- IO === //
  
  public synchronized void addMessage(Result msg) {
    ownMessages.addElement(msg);
  }

  public synchronized boolean say(Agent agent, Result result) throws AmbitException {
    if (!ownAgents.contains(agent)) {return false;} // arbitrates race
    ownMessages.addElement(result);
    notifyAll();
    scream("Say " + result.toString()); // -- trace
    return true;
  }
  
  public synchronized Result ask(Agent agent) throws AmbitException {
    if (!ownAgents.contains(agent)) {return null;} // arbitrates race
    if (!ownMessages.isEmpty()) {
      Result result = (Result)ownMessages.firstElement();
      ownMessages.removeElement(result);
      scream("Ask received " + result.toString()); // -- trace
      return result;   
    } else {
      try {wait();} catch (InterruptedException ex) {}
      return null;
    }
  }

  // === String output === //
  
  public void scream(String screamMsg) {
    long now = System.currentTimeMillis();
    if (screamMsg.equals("")) { screamMsg = console.getState(); }
    // this may actually be a race.
          console.appendOutput(name.toString() + ": " + screamMsg  
          //-- + "  @" + Long.toString(now) 
          + "\n");
  }

  public String toString() {
    // Unsynchronized, just for debugging: can display an inconsistent configuration.
                        String string = name.toString() + "[";
    Enumeration enumAgents = ownAgents.elements();
    boolean hasAgents = enumAgents.hasMoreElements();
    while (enumAgents.hasMoreElements()) {
      string += ((Agent)enumAgents.nextElement()).toString();
      if (enumAgents.hasMoreElements()) { string += " | "; }
    }    
    Enumeration enumAmbients = ownAmbients.elements();
    boolean hasAmbients = enumAmbients.hasMoreElements();
    if (hasAgents && hasAmbients) { string += " | "; }
    while (enumAmbients.hasMoreElements()) {
      string += ((Ambient)enumAmbients.nextElement()).toString();
      if (enumAmbients.hasMoreElements()) { string += " | "; }
    }    
    Enumeration enumMessages = ownMessages.elements();
    boolean hasMessages = enumMessages.hasMoreElements();
    if ((hasAgents || hasAmbients) && hasMessages) { string += " | "; }
    while (enumMessages.hasMoreElements()) {
      string += "say " + ((Result)enumMessages.nextElement()).toString();
      if (enumMessages.hasMoreElements()) { string += " | "; }
    }
    string += "]";
    return string;
  }
  
}

