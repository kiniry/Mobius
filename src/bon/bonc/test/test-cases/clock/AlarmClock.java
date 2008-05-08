/**
 * A clock with an alarm.
 * @title         "TickTockClock"
 * @date          "2007/01/24 11:05:33"
 * @author        "Fintan Fairmichael"
 * @organisation  "School of Computer Science and Informatics, UCD"
 * @copyright     "Copyright (C) 2007 UCD"
 * @version       "$ Revision: 1.23 $"
 */
class AlarmClock extends Clock {
  //@ public model int _alarmTime;
  //@ private represents _alarmTime = alarmMinute*60 + alarmHour*60*60;

  /** The alarm time, in hours. */
  private int alarmHour; //@ in _alarmTime;
  //@ private invariant 0 <= alarmHour && alarmHour <= 23;

  /** The alarm time, in minutes. */
  private int alarmMinute; //@ in _alarmTime;
  //@ private invariant 0 <= alarmMinute && alarmMinute <= 59;

  /** The alarm to be turned on at the alarm time. */
  private /*@ non_null spec_public @*/ AlarmInterface alarm;

  /**
   * Create a new initialised alarm clock associated with the given alarm.
   * @param alarm The alarm to be associated with this new alarm clock.
   */
  public /*@ pure @*/ AlarmClock(/*@ non_null @*/ AlarmInterface alarm) {
    this.alarm = alarm;
  }

  /**
   * Set the alarm time of this clock.
   * @param hour The new alarm time hour.
   * @param minute The new alarm time minute.
   */ 
  //@ requires 0 <= hour && hour <= 23;
  //@ requires 0 <= minute && minute <= 59;
  //@ assignable _alarmTime;
  public void setAlarmTime(int hour, int minute) {
    alarmHour = hour;
    alarmMinute = minute;
  }

  /**
   * One second has passed; update this clock's time and check if we
   * need to switch our alarm on/off.
   * @overrides Alarm.tick()
   */
  //@ also
  //@ ensures _time == _alarmTime ==> alarm.isOn();
  //@ ensures (* If it is the alarm time, the alarm is turned on. *);
  //@ ensures _time == (_alarmTime + 60) % 24*60*60 ==> !alarm.isOn();
  //@ ensures (* If it is one minute after the alarm time, the alarm is turned off. *);
  public void tick() {
    super.tick();
    if (getHour() == alarmHour & getMinute() == alarmMinute & getSecond() == 0)
      alarm.on();
    if ((getHour() == alarmHour & getMinute() == alarmMinute + 1 & getSecond() == 0) ||
        (getHour() == (alarmHour + 1) % 24 &
         alarmMinute == 59 & getMinute() == 0 & getSecond() == 0))
      alarm.off();
  }
}
