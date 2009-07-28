// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

public class Route extends Result {

  public Result step;
  public Route next;

  public Route(Result step, Route next) {
    this.step = step;
    this.next = next;        
  }
  
  public Route append(Route other) {
    if (next == null) {
      return new Route(step, other);
    } else {
      return new Route(step, next.append(other));
    }
  }

  public String toString() {
    String str = step.toString();
    if (next != null) { str += " & " + next.toString(); }
    return str;
  }
    
}
