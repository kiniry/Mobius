// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

public class OutCap extends Cap {
// An output capability.

  // === Instance Variables ===
  
  private String name; // Fixed. The name of the capability.
  private int outCap; // Fixed. The output capability.
  
  // === Constructors ===

  public OutCap(String name, int outCap) {
    this.name = name;
    this.outCap = outCap;
  }
  
  // === Methods ===
  
  public String getName() {
    return name;
  } 
  
  public int getCap () {
    return outCap;
  }
  
  public String toString() {
    return "out " + name;
  } 
  
}
