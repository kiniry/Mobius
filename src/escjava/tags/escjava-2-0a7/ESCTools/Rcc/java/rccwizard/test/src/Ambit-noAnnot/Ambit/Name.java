// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import java.util.Random;

public class Name extends Result {
// The name of an ambient.

  // === Class Variables ===
  
  private static Random rand = new Random();

  // === Instance Variables ===
  
  private String name; // Fixed. The name of an ambient, just for printing.
  private int inCap; // Fixed. The input capability.
  private int outCap; // Fixed. The output capability.
  private int openCap; // Fixed. The open capability.
  private int secret; // Fixed. To differentiate from the set of capabilities.
  
  // === Constructors ===

  public Name(String name) {
    this.name = name;
    this.inCap = rand.nextInt();
    this.outCap = rand.nextInt();
    this.openCap = rand.nextInt();
    this.secret = rand.nextInt();
  }
  
  // === Methods ===
  
  public InCap getInCap() {
    return new InCap(name, inCap);
  }
  
  public OutCap getOutCap() {
    return new OutCap(name, outCap);
  }
  
  public OpenCap getOpenCap() {
    return new OpenCap(name, openCap);
  }
  
  public boolean matches(Name other) {
    return (secret == other.secret);
  }
  
  public boolean matches(Cap otherCap) {
    if (otherCap instanceof InCap) {
      return (inCap == otherCap.getCap());
    } else if (otherCap instanceof OutCap) {
      return (outCap == otherCap.getCap());
    } else if (otherCap instanceof OpenCap) {
      return (openCap == otherCap.getCap());
    } else {
      return false;
    }
  }
  
  public boolean matches(String str) {
    return name.equals(str);
  }
  
  public String toString() {
    return name;
  } 
  
}
