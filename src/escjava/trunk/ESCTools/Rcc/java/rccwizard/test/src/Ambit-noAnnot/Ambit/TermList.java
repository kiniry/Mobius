// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;
import Parser.Synex.Parser.OutcomeLocated;

public class TermList extends OutcomeLocated {

  public CodeTerm term;
  public TermList next;

  public TermList(CodeTerm term, TermList next, Location begLocation, Location endLocation) {
    super(begLocation, endLocation);
    this.term = term;
    this.next = next;        
  }

  public String toString() {
    String str = term.toString() + "  ";
    if (next != null) { str += next.toString(); }
    return str;
  }
    
}
