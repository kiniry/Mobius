class AlarmClock extends Clock {
  //@ public model int _alarmTime;
  //@ private represents _alarmTime = alarmMinute*60 + alarmHour*60*60;

  //@ public ghost boolean _alarm_going_off = false; //@ in _time;
  
  //@ private invariant 0 <= alarmHour && alarmHour <= 23;
  private int alarmHour; //@ in _alarmTime;

  //@ private invariant 0 <= alarmMinute && alarmMinute <= 59;
  private int alarmMinute; //@ in _alarmTime;

  private /*@ non_null @*/ AlarmInterface alarm;

  public /*@ pure @*/ AlarmClock(/*@ non_null @*/ AlarmInterface alarm) {
    this.alarm = alarm;
  }

  /*@ requires 0 <= hour && hour <= 23;
    @ requires 0 <= minute && minute <= 59;
    @ assignable _alarmTime;
    @*/
  public void setAlarmTime(int hour, int minute) {
    alarmHour = hour;
    alarmMinute = minute;
  }

  // spec inherited from superclass Clock
  public void tick() {
    super.tick();
    if (getHour() == alarmHour & getMinute() == alarmMinute & getSecond() == 0) {
         alarm.on();
         //@ set _alarm_going_off = true;
    }
    if ((getHour() == alarmHour & getMinute() == alarmMinute+1 & getSecond() == 0) 
        ||
        (getHour() == alarmHour+1 & alarmMinute == 59 & getSecond() == 0) ) {
         alarm.off();
         //@ set _alarm_going_off = false;
    }
  }

}
