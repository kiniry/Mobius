/**
 * An alarm that is either on or off.
 * @title         "TickTockClock"
 * @date          "2007/01/21 19:23:13"
 * @author        "Fintan Fairmichael"
 * @organisation  "School of Computer Science and Informatics, UCD"
 * @copyright     "Copyright (C) 2007 UCD"
 * @version       "$ Revision: 1.3 $"
 */
public interface AlarmInterface {
  /** Turn this alarm on. */
  //@ ensures isOn();
  public void on();
	
  /** Turn this alarm off. */
  //@ ensures !isOn();
  public void off();
	
  /** @returns Is this alarm on? */
  public /*@ pure @*/ boolean isOn();
}
