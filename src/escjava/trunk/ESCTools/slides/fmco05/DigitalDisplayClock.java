public class DigitalDisplayClock { 
   //@ public model long _time;                                    
   //@ private represents _time = getSecond() + getMinute()*60 + getHour()*60*60; 

    //@ private invariant time.length == 6;
    //@ private invariant 0 <= time[0] && time[0] <= 9; // sec
    //@ private invariant 0 <= time[1] && time[1] <= 5; // sec
    //@ private invariant 0 <= time[2] && time[2] <= 9; // min
    //@ private invariant 0 <= time[3] && time[3] <= 5; // min
    //@ private invariant 0 <= time[4] && time[4] <= 9; // hr
    //@ private invariant 0 <= time[5] && time[5] <= 2; // hr
    //@ private invariant time[5] == 2 ==> time[4] <= 3; // hr
    private /*@ non_null rep @*/ int[] time;  // rep modifier to prevent aliasing 

    /*@ pure @*/ public DigitalDisplayClock() { time = new /*@ rep @*/ rep int [6]; }   // note rep modifier

    //@ ensures 0 <= \result && \result <= 23;
    public /*@ pure @*/ int getHour() { return  time[5]*10 + time[4]; }

    //@ ensures 0 <= \result && \result <= 59;
    public /*@ pure @*/ int getMinute() { return time[3]*10 + time[2]; }

    //@ ensures 0 <= \result && \result <= 59;
    public /*@ pure @*/ int getSecond() { return time[1]*10 + time[0]; }
 
    /*@ requires 0 <= hour && hour <= 23 && 0 <= minute && minute <= 59;
      @ assignable _time;
      @ ensures getHour() == hour && getMinute() == minute && getSecond() == 0;
      @*/
    public void setTime(int hour, int minute) {
        time[5] = hour / 10;    time[4] = hour % 10;
        time[3] = minute % 10;  time[2] = minute % 10;
        time[1] = 0 ;           time[0] = 0;
    }

    //@ assignable _time;
    //@ ensures _time == (\old(_time)+1) % 24*60*60;
    public void tick() {
        time[0]++;
        if (time[0] == 10) { time[0] = 0; time[1]++; }
        if (time[1] == 6)  { time[1] = 0; time[2]++; } // minute passed
        if (time[2] == 10) { time[2] = 0; time[3]++; }
        if (time[3] == 6)  { time[3] = 0; time[4]++; } // hour passed
        if (time[4] == 10) { time[4] = 0; time[3]++; }
        if (time[5] == 2 && time[4] == 4)
            { time[5] = 0; time[4] = 0; } // day passed
    }
}
