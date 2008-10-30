abstract class P {
  private int x, y;
  
  
  /*@ requires t != null;
   	  ensures \result.x == \old(x) + t.x &&
              \result.y == \old(y) + t.y; @*/
  public P translate (P t) {
    x += t.x;
    y += t.y;
    return this;
  }
}
