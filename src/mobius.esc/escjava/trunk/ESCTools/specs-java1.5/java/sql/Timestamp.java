package java.sql;

public class Timestamp extends java.util.Date {
    
    
    public Timestamp(int year, int month, int date, int hour, int minute, int second, int nano) {
        super(year, month, date, hour, minute, second);
        if (nano > 999999999 || nano < 0) {
            throw new IllegalArgumentException("nanos > 999999999 or < 0");
        }
        nanos = nano;
    }
    
    public Timestamp(long time) {
        super((time / 1000) * 1000);
        nanos = (int)((time % 1000) * 1000000);
        if (nanos < 0) {
            nanos = 1000000000 + nanos;
            super.setTime(((time / 1000) - 1) * 1000);
        }
    }
    
    public void setTime(long time) {
        super.setTime((time / 1000) * 1000);
        nanos = (int)((time % 1000) * 1000000);
        if (nanos < 0) {
            nanos = 1000000000 + nanos;
            super.setTime(((time / 1000) - 1) * 1000);
        }
    }
    
    public long getTime() {
        long time = super.getTime();
        return (time + (nanos / 1000000));
    }
    private int nanos;
    
    public static Timestamp valueOf(String s) {
        String date_s;
        String time_s;
        String nanos_s;
        int year;
        int month;
        int day;
        int hour;
        int minute;
        int second;
        int a_nanos = 0;
        int firstDash;
        int secondDash;
        int dividingSpace;
        int firstColon = 0;
        int secondColon = 0;
        int period = 0;
        String formatError = "Timestamp format must be yyyy-mm-dd hh:mm:ss.fffffffff";
        String zeros = "000000000";
        if (s == null) throw new java.lang.IllegalArgumentException("null string");
        s = s.trim();
        dividingSpace = s.indexOf(' ');
        if (dividingSpace > 0) {
            date_s = s.substring(0, dividingSpace);
            time_s = s.substring(dividingSpace + 1);
        } else {
            throw new java.lang.IllegalArgumentException(formatError);
        }
        firstDash = date_s.indexOf('-');
        secondDash = date_s.indexOf('-', firstDash + 1);
        if (time_s == null) throw new java.lang.IllegalArgumentException(formatError);
        firstColon = time_s.indexOf(':');
        secondColon = time_s.indexOf(':', firstColon + 1);
        period = time_s.indexOf('.', secondColon + 1);
        if ((firstDash > 0) & (secondDash > 0) & (secondDash < date_s.length() - 1)) {
            year = Integer.parseInt(date_s.substring(0, firstDash)) - 1900;
            month = Integer.parseInt(date_s.substring(firstDash + 1, secondDash)) - 1;
            day = Integer.parseInt(date_s.substring(secondDash + 1));
        } else {
            throw new java.lang.IllegalArgumentException(formatError);
        }
        if ((firstColon > 0) & (secondColon > 0) & (secondColon < time_s.length() - 1)) {
            hour = Integer.parseInt(time_s.substring(0, firstColon));
            minute = Integer.parseInt(time_s.substring(firstColon + 1, secondColon));
            if ((period > 0) & (period < time_s.length() - 1)) {
                second = Integer.parseInt(time_s.substring(secondColon + 1, period));
                nanos_s = time_s.substring(period + 1);
                if (nanos_s.length() > 9) throw new java.lang.IllegalArgumentException(formatError);
                if (!Character.isDigit(nanos_s.charAt(0))) throw new java.lang.IllegalArgumentException(formatError);
                nanos_s = nanos_s + zeros.substring(0, 9 - nanos_s.length());
                a_nanos = Integer.parseInt(nanos_s);
            } else if (period > 0) {
                throw new java.lang.IllegalArgumentException(formatError);
            } else {
                second = Integer.parseInt(time_s.substring(secondColon + 1));
            }
        } else {
            throw new java.lang.IllegalArgumentException();
        }
        return new Timestamp(year, month, day, hour, minute, second, a_nanos);
    }
    
    public String toString() {
        int year = super.getYear() + 1900;
        int month = super.getMonth() + 1;
        int day = super.getDate();
        int hour = super.getHours();
        int minute = super.getMinutes();
        int second = super.getSeconds();
        String yearString;
        String monthString;
        String dayString;
        String hourString;
        String minuteString;
        String secondString;
        String nanosString;
        String zeros = "000000000";
        String yearZeros = "0000";
        StringBuffer timestampBuf;
        if (year < 1000) {
            yearString = "" + year;
            yearString = yearZeros.substring(0, (4 - yearString.length())) + yearString;
        } else {
            yearString = "" + year;
        }
        if (month < 10) {
            monthString = "0" + month;
        } else {
            monthString = Integer.toString(month);
        }
        if (day < 10) {
            dayString = "0" + day;
        } else {
            dayString = Integer.toString(day);
        }
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
        if (nanos == 0) {
            nanosString = "0";
        } else {
            nanosString = Integer.toString(nanos);
            nanosString = zeros.substring(0, (9 - nanosString.length())) + nanosString;
            char[] nanosChar = new char[nanosString.length()];
            nanosString.getChars(0, nanosString.length(), nanosChar, 0);
            int truncIndex = 8;
            while (nanosChar[truncIndex] == '0') {
                truncIndex--;
            }
            nanosString = new String(nanosChar, 0, truncIndex + 1);
        }
        timestampBuf = new StringBuffer();
        timestampBuf.append(yearString);
        timestampBuf.append("-");
        timestampBuf.append(monthString);
        timestampBuf.append("-");
        timestampBuf.append(dayString);
        timestampBuf.append(" ");
        timestampBuf.append(hourString);
        timestampBuf.append(":");
        timestampBuf.append(minuteString);
        timestampBuf.append(":");
        timestampBuf.append(secondString);
        timestampBuf.append(".");
        timestampBuf.append(nanosString);
        return (timestampBuf.toString());
    }
    
    public int getNanos() {
        return nanos;
    }
    
    public void setNanos(int n) {
        if (n > 999999999 || n < 0) {
            throw new IllegalArgumentException("nanos > 999999999 or < 0");
        }
        nanos = n;
    }
    
    public boolean equals(Timestamp ts) {
        if (super.equals(ts)) {
            if (nanos == ts.nanos) {
                return true;
            } else {
                return false;
            }
        } else {
            return false;
        }
    }
    
    public boolean equals(java.lang.Object ts) {
        if (ts instanceof Timestamp) {
            return this.equals((Timestamp)(Timestamp)ts);
        } else {
            return false;
        }
    }
    
    public boolean before(Timestamp ts) {
        return compareTo(ts) < 0;
    }
    
    public boolean after(Timestamp ts) {
        return compareTo(ts) > 0;
    }
    
    public int compareTo(Timestamp ts) {
        int i = super.compareTo(ts);
        if (i == 0) {
            if (nanos > ts.nanos) {
                return 1;
            } else if (nanos < ts.nanos) {
                return -1;
            }
        }
        return i;
    }
    
    public int compareTo(java.util.Date o) {
        if (o instanceof Timestamp) {
            return compareTo((Timestamp)(Timestamp)o);
        } else {
            Timestamp ts = new Timestamp(o.getTime());
            return this.compareTo(ts);
        }
    }
    static final long serialVersionUID = 2745179027874758501L;
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((java.util.Date)x0);
    }
}
