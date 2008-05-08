/**
 * A logical clock.
 * @title         "TickTockClock"
 * @date          "2007/01/23 18:00:49"
 * @author        "Fintan Fairmichael"
 * @organisation  "School of Computer Science and Informatics, UCD"
 * @copyright     "Copyright (C) 2007 UCD"
 * @version       "$ Revision: 1.7 $"
 */

public interface LogicalClock {
  // The current time of this clock.
  //@ public model instance \bigint _time;

  //@ public invariant _time >= 0; 

  /**
   * @returns What is the current time of this clock?
   * @concurrency CONCURRENT 
   */
  //@ ensures \result == _time;
  public /*@ pure @*/ long getLogicalTime();

  /**
   * Advance this clock's time.
   * @concurrency GUARDED
   */
  //@ assignable _time;
  //@ ensures \old( _time ) > _time;
  //@ ensures (* _time has been increased. *);
  public void advance();
}