package java.sql;

public class Time extends java.util.Date {
    
    
    public Time(int hour, int minute, int second) {
        super(70, 0, 1, hour, minute, second);
    }
    
    public Time(long time) {
        super(time);
    }
    
    public void setTime(long time) {
        super.setTime(time);
    }
    
    public static Time valueOf(String s) {
        int hour;
        int minute;
        int second;
        int firstColon;
        int secondColon;
        if (s == null) throw new java.lang.IllegalArgumentException();
        firstColon = s.indexOf(':');
        secondColon = s.indexOf(':', firstColon + 1);
        if ((firstColon > 0) & (secondColon > 0) & (secondColon < s.length() - 1)) {
            hour = Integer.parseInt(s.substring(0, firstColon));
            minute = Integer.parseInt(s.substring(firstColon + 1, secondColon));
            second = Integer.parseInt(s.substring(secondColon + 1));
        } else {
            throw new java.lang.IllegalArgumentException();
        }
        return new Time(hour, minute, second);
    }
    
    public String toString() {
        int hour = super.getHours();
        int minute = super.getMinutes();
        int second = super.getSeconds();
        String hourString;
        String minuteString;
        String secondString;
        if (hour < 10) {
            hourString = "0" + hour;
        } else {
            hourString = Integer.toString(hour);
        }
        if (minute < 10) {
            minuteString = "0" + minute;
        } else {
            minuteString = Integer.toString(minute);
        }
        if (second < 10) {
            secondString = "0" + second;
        } else {
            secondString = Integer.toString(second);
        }
        return (hourString + ":" + minuteString + ":" + secondString);
    }
    
    
    public int getYear() {
        throw new java.lang.IllegalArgumentException();
    }
    
    
    public int getMonth() {
        throw new java.lang.IllegalArgumentException();
    }
    
    
    public int getDay() {
        throw new java.lang.IllegalArgumentException();
    }
    
    
    public int getDate() {
        throw new java.lang.IllegalArgumentException();
    }
    
    
    public void setYear(int i) {
        throw new java.lang.IllegalArgumentException();
    }
    
    
    public void setMonth(int i) {
        throw new java.lang.IllegalArgumentException();
    }
    
    
    public void setDate(int i) {
        throw new java.lang.IllegalArgumentException();
    }
    static final long serialVersionUID = 8397324403548013681L;
}
