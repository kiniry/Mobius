// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

public class OpenCap extends Cap {
// An open capability.

  // === Instance Variables ===
  
  private String name; // Fixed. The name of the capability.
  private int openCap; // Fixed. The output capability.
  
  // === Constructors ===

  public OpenCap(String name, int openCap) {
    this.name = name;
    this.openCap = openCap;
  }
  
  // === Methods ===
  
  public String getName() {
    return name;
  } 
  
  public int getCap () {
    return openCap;
  }
  
  public String toString() {
    return "open " + name;
  } 
  
}
