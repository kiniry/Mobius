// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

public class Real extends Result {

  // === Instance Variables ===
  
  public double real;
  
  // === Constructors ===

  public Real(double real) {
    this.real = real;
  }
  
  public String toString() {
    return Double.toString(real);
  } 
  
}
