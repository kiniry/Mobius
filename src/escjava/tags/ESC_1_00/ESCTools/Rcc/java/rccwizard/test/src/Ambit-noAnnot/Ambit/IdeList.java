// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

import Parser.Synex.Scanner.Location;
import Parser.Synex.Parser.OutcomeLocated;

public class IdeList extends OutcomeLocated {

  public String ide;
  public IdeList next;

  public IdeList(String ide, IdeList next, Location begLocation, Location endLocation) {
    super(begLocation, endLocation);
    this.ide = ide;
    this.next = next;        
  }

  public String toString() {
    String str = ide + "  ";
    if (next != null) { str += next.toString(); }
    return str;
  }
    
}
