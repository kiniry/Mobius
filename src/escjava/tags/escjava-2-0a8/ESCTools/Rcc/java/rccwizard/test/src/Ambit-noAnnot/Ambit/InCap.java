// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

public class InCap extends Cap {
// An input capability.

  // === Instance Variables ===
  
  private String name; // Fixed. The name of the capability.
  private int inCap; // Fixed. The input capability.
  
  // === Constructors ===

  public InCap(String name, int inCap) {
    this.name = name;
    this.inCap = inCap;
  }
  
  // === Methods ===
  
  public String getName() {
    return name;
  } 
  
  public int getCap() {
    return inCap;
  }
  
  public String toString() {
    return "in " + name;
  } 
  
}
