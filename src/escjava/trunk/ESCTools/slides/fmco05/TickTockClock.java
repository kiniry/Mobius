//@ model import org.jmlspecs.lang.JMLDataGroup;
public class TickTockClock {
  //@ public model JMLDataGroup _time_state; 

  //@ protected invariant 0 <= hour && hour <= 23;
  protected int hour; //@ in _time_state;
  //@ protected invariant 0 <= minute && minute <= 59;
  protected int minute; //@ in _time_state;
  //@ protected invariant 0 <= second && second <= 59;
  protected int second; //@ in _time_state;

  //@ ensures getHour() == 12  && getMinute() == 0  &&  getSecond() == 0;
  public /*@ pure @*/ TickTockClock() {
      hour = 12; minute = 0; second = 0;
  }

  //@ requires true;
  //@ ensures 0 <= \result && \result <= 23;
  public /*@ pure @*/ int getHour() { return hour; }

  //@ ensures 0 <= \result && \result <= 59;
  public /*@ pure @*/ int getMinute() { return minute; }

  //@ ensures 0 <= \result;
  //@ ensures \result <= 59;
  public /*@ pure @*/ int getSecond() { return second; }

  /*@  requires   getSecond() < 59;
    @  assignable _time_state;
    @  ensures    getSecond() == \old(getSecond() + 1) &&
    @             getMinute() == \old(getMinute()) &&
    @             getHour() == \old(getHour());
    @ also
    @  requires   getSecond() == 59;
    @  assignable _time_state;
    @  ensures    getSecond() == 0 &&
    @           (* hours and minutes are updated appropriately *);
    @*/
  public void tick() {
      second++; 
      if (second == 60) { second = 0; minute++; }
      if (minute == 60) { minute = 0; hour++; }
      if (hour == 24)   { hour = 0; }
  }
}
