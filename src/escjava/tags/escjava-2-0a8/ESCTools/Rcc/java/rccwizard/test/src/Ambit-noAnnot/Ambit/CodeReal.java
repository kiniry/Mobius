// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;

public class CodeReal extends CodeTerm {

  public double real; // The real number.

  public CodeReal(double real, Location begLocation, Location endLocation) {
  // Constructor.
    super(begLocation, endLocation);
    this.real = real;
  }
  
  public Result exec(Agent agent, Env env) throws ExecException {
    return new Real(real);
  }
  
  public String toString() {
    return Double.toString(real);
  }

}
