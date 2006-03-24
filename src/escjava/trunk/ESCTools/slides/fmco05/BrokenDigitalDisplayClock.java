class MyDigitalDisplayClock extends DigitalDisplayClock{

  //@ requires time.length == 6;
  /*@ pure @*/ public BrokenDigitalDisplayClock( /*@ non_null @*/ int[] time) { 
     this.time = time; 
  }

  public /*@ pure @*/ int[] expose() { return time; } 
}
