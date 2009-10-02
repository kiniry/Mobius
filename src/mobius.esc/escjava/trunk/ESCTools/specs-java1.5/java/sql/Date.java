package java.sql;

public class Date extends java.util.Date {
    
    
    public Date(int year, int month, int day) {
        super(year, month, day);
    }
    
    public Date(long date) {
        super(date);
    }
    
    public void setTime(long date) {
        super.setTime(date);
    }
    
    public static Date valueOf(String s) {
        int year;
        int month;
        int day;
        int firstDash;
        int secondDash;
        if (s == null) throw new java.lang.IllegalArgumentException();
        firstDash = s.indexOf('-');
        secondDash = s.indexOf('-', firstDash + 1);
        if ((firstDash > 0) & (secondDash > 0) & (secondDash < s.length() - 1)) {
            year = Integer.parseInt(s.substring(0, firstDash)) - 1900;
            month = Integer.parseInt(s.substring(firstDash + 1, secondDash)) - 1;
            day = Integer.parseInt(s.substring(secondDash + 1));
        } else {
            throw new java.lang.IllegalArgumentException();
        }
        return new Date(year, month, day);
    }
    
    public String toString() {
        int year = super.getYear() + 1900;
        int month = super.getMonth() + 1;
        int day = super.getDate();
        char[] buf = "2000-00-00".toCharArray();
        buf[0] = Character.forDigit(year / 1000, 10);
        buf[1] = Character.forDigit((year / 100) % 10, 10);
        buf[2] = Character.forDigit((year / 10) % 10, 10);
        buf[3] = Character.forDigit(year % 10, 10);
        buf[5] = Character.forDigit(month / 10, 10);
        buf[6] = Character.forDigit(month % 10, 10);
        buf[8] = Character.forDigit(day / 10, 10);
        buf[9] = Character.forDigit(day % 10, 10);
        return new String(buf);
    }
    
    
    public int getHours() {
        throw new java.lang.IllegalArgumentException();
    }
    
    
    public int getMinutes() {
        throw new java.lang.IllegalArgumentException();
    }
    
    
    public int getSeconds() {
        throw new java.lang.IllegalArgumentException();
    }
    
    
    public void setHours(int i) {
        throw new java.lang.IllegalArgumentException();
    }
    
    
    public void setMinutes(int i) {
        throw new java.lang.IllegalArgumentException();
    }
    
    
    public void setSeconds(int i) {
        throw new java.lang.IllegalArgumentException();
    }
    static final long serialVersionUID = 1511598038487230103L;
}
