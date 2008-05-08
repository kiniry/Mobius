/**
 * A settable clock storing the time in hours, minutes and seconds.
 * @title         "TickTockClock"
 * @date          "2007/01/23 14:03:55"
 * @author        "Fintan Fairmichael"
 * @organisation  "School of Computer Science and Informatics, UCD"
 * @copyright     "Copyright (C) 2007 UCD"
 * @version       "$ Revision: 1.17 $"
 */
public class Clock {
  //@ public model long _time;
  //@ private represents _time = second + minute*60 + hour*60*60;

  //@ public invariant _time == getSecond() + getMinute()*60 + getHour()*60*60;
  //@ public invariant 0 <= _time && _time < 24*60*60;

  /** The current time of this clock, in hours. */
  private int hour; //@ in _time;
  //@ private invariant 0 <= hour && hour <= 23;

  /** The current time of this clock, in minutes. */
  private int minute; //@ in _time;
  //@ private invariant 0 <= minute && minute <= 59;

  /** The current time of this clock, in seconds. */
  private int second; //@ in _time;
  //@ private invariant 0 <= second && second <= 59;

  /** Create a new clock, initialised with time 12:00. */
  //@ ensures _time == 12*60*60;
  public /*@ pure @*/ Clock() { hour = 12; minute = 0; second = 0; }

  /** @returns What is the current hour value? */
  //@ ensures 0 <= \result && \result <= 23;
  public /*@ pure @*/ int getHour() { return hour; }

  /** @returns What is the current minute value? */
  //@ ensures 0 <= \result && \result <= 59;
  public /*@ pure @*/ int getMinute() { return minute; }

  /** @returns What is the current second value? */
  //@ ensures 0 <= \result && \result <= 59;
  public /*@ pure @*/ int getSecond() { return second; }

  /**
   * Set this clock to a new time.
   * @param hour This clock's new hour value.
   * @param minute This clock's new minute value.
   */
  //@ requires   0 <= hour && hour <= 23;
  //@ requires   0 <= minute && minute <= 59;
  //@ assignable _time;
  //@ ensures    _time == hour*60*60 + minute*60;
  public void setTime(int hour, int minute) {
    this.hour = hour; this.minute = minute; this.second = 0;
  }

  /** One second has passed; update this clock's time. */
  //@ assignable _time;
  //@ ensures _time == \old(_time + 1) % 24*60*60;
  //@ ensures (* The new time is one second ahead of the old, wrapping 24:00 *);
  //@ ensures (* back to 00:00. *);
  public void tick() {
    second++;
    if (second == 60) { second = 0; minute++; }
    if (minute == 60) { minute = 0; hour++; }
    if (hour == 24)   { hour = 0; }
  }

}
