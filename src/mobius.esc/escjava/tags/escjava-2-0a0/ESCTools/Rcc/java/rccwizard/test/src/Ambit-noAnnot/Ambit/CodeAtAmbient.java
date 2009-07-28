// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;
import Parser.Synex.Parser.OutcomeLocated;

public class CodeAtAmbient extends OutcomeLocated {

  public String path; // The path to the ambient from root.
  public CodeProc proc; // The code to run in the ambient.

  public CodeAtAmbient(String path, CodeProc proc, Location begLocation, Location endLocation) {
    super(begLocation, endLocation);
    this.path = path;
    this.proc = proc;
  }
  
  public String toString() {
    return "at " + path + "." + proc.toString();
  }
  
}
