class SettableClock extends TickTockClock {

    // ...

    /*@ public normal_behavior
      @   requires 0 <= hour && hour <= 23 &&
      @            0 <= minute && minute <= 59;
      @   assignable _time_state;
      @   ensures  getHour() == hour &&
      @            getMinute() == minute && getSecond() == 0;
      @ also
      @  public exceptional_behavior
      @   requires !(0 <= hour && hour <= 23 &&
      @              0 <= minute && minute <= 59);
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @   signals_only IllegalArgumentException;
      @*/
    public void setTime(int hour, int minute) {
        if(!(0 <= hour && hour <= 23 && 0 <= minute && minute <= 59)){
             throw new IllegalArgumentException();
	}
        this.hour = hour; 
	this.minute = minute; 
	this.second = 0;
    }
}
