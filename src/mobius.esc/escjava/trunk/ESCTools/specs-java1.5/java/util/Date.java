package java.util;

import java.text.DateFormat;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import sun.util.calendar.BaseCalendar;
import sun.util.calendar.CalendarSystem;
import sun.util.calendar.CalendarUtils;
import sun.util.calendar.ZoneInfo;

public class Date implements java.io.Serializable, Cloneable, Comparable {
    private static final BaseCalendar gcal = CalendarSystem.getGregorianCalendar();
    private static BaseCalendar jcal;
    private transient long fastTime;
    private transient BaseCalendar$Date cdate;
    private static int defaultCenturyStart;
    private static final long serialVersionUID = 7523967970034938905L;
    
    public Date() {
        this(System.currentTimeMillis());
    }
    
    public Date(long date) {
        
        fastTime = date;
    }
    
    //
    public Date(int year, int month, int date) {
        this(year, month, date, 0, 0, 0);
    }
    
    //
    public Date(int year, int month, int date, int hrs, int min) {
        this(year, month, date, hrs, min, 0);
    }
    
    //
    public Date(int year, int month, int date, int hrs, int min, int sec) {
        
        int y = year + 1900;
        if (month >= 12) {
            y += month / 12;
            month %= 12;
        } else if (month < 0) {
            y += CalendarUtils.floorDivide(month, 12);
            month = CalendarUtils.mod(month, 12);
        }
        BaseCalendar cal = getCalendarSystem(y);
        cdate = (BaseCalendar$Date)(BaseCalendar$Date)cal.newCalendarDate(TimeZone.getDefaultRef());
        cdate.setNormalizedDate(y, month + 1, date).setTimeOfDay(hrs, min, sec, 0);
        getTimeImpl();
        cdate = null;
    }
    
    //
    public Date(String s) {
        this(parse(s));
    }
    
    public Object clone() {
        Date d = null;
        try {
            d = (Date)(Date)super.clone();
            if (cdate != null) {
                d.cdate = (BaseCalendar$Date)(BaseCalendar$Date)cdate.clone();
            }
        } catch (CloneNotSupportedException e) {
        }
        return d;
    }
    
    //
    public static long UTC(int year, int month, int date, int hrs, int min, int sec) {
        int y = year + 1900;
        if (month >= 12) {
            y += month / 12;
            month %= 12;
        } else if (month < 0) {
            y += CalendarUtils.floorDivide(month, 12);
            month = CalendarUtils.mod(month, 12);
        }
        int m = month + 1;
        BaseCalendar cal = getCalendarSystem(y);
        BaseCalendar$Date udate = (BaseCalendar$Date)(BaseCalendar$Date)cal.newCalendarDate(null);
        udate.setNormalizedDate(y, m, date).setTimeOfDay(hrs, min, sec, 0);
        Date d = new Date(0);
        d.normalize(udate);
        return d.fastTime;
    }
    
    //
    public static long parse(String s) {
        int year = Integer.MIN_VALUE;
        int mon = -1;
        int mday = -1;
        int hour = -1;
        int min = -1;
        int sec = -1;
        int millis = -1;
        int c = -1;
        int i = 0;
        int n = -1;
        int wst = -1;
        int tzoffset = -1;
        int prevc = 0;
        syntax: {
            if (s == null) break syntax;
            int limit = s.length();
            while (i < limit) {
                c = s.charAt(i);
                i++;
                if (c <= ' ' || c == ',') continue;
                if (c == '(') {
                    int depth = 1;
                    while (i < limit) {
                        c = s.charAt(i);
                        i++;
                        if (c == '(') depth++; else if (c == ')') if (--depth <= 0) break;
                    }
                    continue;
                }
                if ('0' <= c && c <= '9') {
                    n = c - '0';
                    while (i < limit && '0' <= (c = s.charAt(i)) && c <= '9') {
                        n = n * 10 + c - '0';
                        i++;
                    }
                    if (prevc == '+' || prevc == '-' && year != Integer.MIN_VALUE) {
                        if (n < 24) n = n * 60; else n = n % 100 + n / 100 * 60;
                        if (prevc == '+') n = -n;
                        if (tzoffset != 0 && tzoffset != -1) break syntax;
                        tzoffset = n;
                    } else if (n >= 70) if (year != Integer.MIN_VALUE) break syntax; else if (c <= ' ' || c == ',' || c == '/' || i >= limit) year = n; else break syntax; else if (c == ':') if (hour < 0) hour = (byte)n; else if (min < 0) min = (byte)n; else break syntax; else if (c == '/') if (mon < 0) mon = (byte)(n - 1); else if (mday < 0) mday = (byte)n; else break syntax; else if (i < limit && c != ',' && c > ' ' && c != '-') break syntax; else if (hour >= 0 && min < 0) min = (byte)n; else if (min >= 0 && sec < 0) sec = (byte)n; else if (mday < 0) mday = (byte)n; else if (year == Integer.MIN_VALUE && mon >= 0 && mday >= 0) year = n; else break syntax;
                    prevc = 0;
                } else if (c == '/' || c == ':' || c == '+' || c == '-') prevc = c; else {
                    int st = i - 1;
                    while (i < limit) {
                        c = s.charAt(i);
                        if (!('A' <= c && c <= 'Z' || 'a' <= c && c <= 'z')) break;
                        i++;
                    }
                    if (i <= st + 1) break syntax;
                    int k;
                    for (k = wtb.length; --k >= 0; ) if (wtb[k].regionMatches(true, 0, s, st, i - st)) {
                        int action = ttb[k];
                        if (action != 0) {
                            if (action == 1) {
                                if (hour > 12 || hour < 1) break syntax; else if (hour < 12) hour += 12;
                            } else if (action == 14) {
                                if (hour > 12 || hour < 1) break syntax; else if (hour == 12) hour = 0;
                            } else if (action <= 13) {
                                if (mon < 0) mon = (byte)(action - 2); else break syntax;
                            } else {
                                tzoffset = action - 10000;
                            }
                        }
                        break;
                    }
                    if (k < 0) break syntax;
                    prevc = 0;
                }
            }
            if (year == Integer.MIN_VALUE || mon < 0 || mday < 0) break syntax;
            if (year < 100) {
                synchronized (Date.class) {
                    if (defaultCenturyStart == 0) {
                        defaultCenturyStart = gcal.getCalendarDate().getYear() - 80;
                    }
                }
                year += (defaultCenturyStart / 100) * 100;
                if (year < defaultCenturyStart) year += 100;
            }
            if (sec < 0) sec = 0;
            if (min < 0) min = 0;
            if (hour < 0) hour = 0;
            BaseCalendar cal = getCalendarSystem(year);
            if (tzoffset == -1) {
                BaseCalendar$Date ldate = (BaseCalendar$Date)(BaseCalendar$Date)cal.newCalendarDate(TimeZone.getDefaultRef());
                ldate.setDate(year, mon + 1, mday);
                ldate.setTimeOfDay(hour, min, sec, 0);
                return cal.getTime(ldate);
            }
            BaseCalendar$Date udate = (BaseCalendar$Date)(BaseCalendar$Date)cal.newCalendarDate(null);
            udate.setDate(year, mon + 1, mday);
            udate.setTimeOfDay(hour, min, sec, 0);
            return cal.getTime(udate) + tzoffset * (60 * 1000);
        }
        throw new IllegalArgumentException();
    }
    private static final String[] wtb = {"am", "pm", "monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday", "january", "february", "march", "april", "may", "june", "july", "august", "september", "october", "november", "december", "gmt", "ut", "utc", "est", "edt", "cst", "cdt", "mst", "mdt", "pst", "pdt"};
    private static final int[] ttb = {14, 1, 0, 0, 0, 0, 0, 0, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 10000 + 0, 10000 + 0, 10000 + 0, 10000 + 5 * 60, 10000 + 4 * 60, 10000 + 6 * 60, 10000 + 5 * 60, 10000 + 7 * 60, 10000 + 6 * 60, 10000 + 8 * 60, 10000 + 7 * 60};
    
    
    public int getYear() {
        return normalize().getYear() - 1900;
    }
    
    
    public void setYear(int year) {
        getCalendarDate().setNormalizedYear(year + 1900);
    }
    
    
    public int getMonth() {
        return normalize().getMonth() - 1;
    }
    
    
    public void setMonth(int month) {
        int y = 0;
        if (month >= 12) {
            y = month / 12;
            month %= 12;
        } else if (month < 0) {
            y = CalendarUtils.floorDivide(month, 12);
            month = CalendarUtils.mod(month, 12);
        }
        BaseCalendar$Date d = getCalendarDate();
        if (y != 0) {
            d.setNormalizedYear(d.getNormalizedYear() + y);
        }
        d.setMonth(month + 1);
    }
    
    
    public int getDate() {
        return normalize().getDayOfMonth();
    }
    
    
    public void setDate(int date) {
        getCalendarDate().setDayOfMonth(date);
    }
    
    
    public int getDay() {
        return normalize().getDayOfWeek() - gcal.SUNDAY;
    }
    
    
    public int getHours() {
        return normalize().getHours();
    }
    
    
    public void setHours(int hours) {
        getCalendarDate().setHours(hours);
    }
    
    
    public int getMinutes() {
        return normalize().getMinutes();
    }
    
    
    public void setMinutes(int minutes) {
        getCalendarDate().setMinutes(minutes);
    }
    
    
    public int getSeconds() {
        return normalize().getSeconds();
    }
    
    
    public void setSeconds(int seconds) {
        getCalendarDate().setSeconds(seconds);
    }
    
    public long getTime() {
        return getTimeImpl();
    }
    
    private final long getTimeImpl() {
        if (cdate != null && !cdate.isNormalized()) {
            normalize();
        }
        return fastTime;
    }
    
    public void setTime(long time) {
        fastTime = time;
        cdate = null;
    }
    
    public boolean before(Date when) {
        return getMillisOf(this) < getMillisOf(when);
    }
    
    public boolean after(Date when) {
        return getMillisOf(this) > getMillisOf(when);
    }
    
    public boolean equals(Object obj) {
        return obj instanceof Date && getTime() == ((Date)(Date)obj).getTime();
    }
    
    static final long getMillisOf(Date date) {
        if (date.cdate == null) {
            return date.fastTime;
        }
        BaseCalendar$Date d = (BaseCalendar$Date)(BaseCalendar$Date)date.cdate.clone();
        return gcal.getTime(d);
    }
    
    public int compareTo(Date anotherDate) {
        long thisTime = getMillisOf(this);
        long anotherTime = getMillisOf(anotherDate);
        return (thisTime < anotherTime ? -1 : (thisTime == anotherTime ? 0 : 1));
    }
    
    public int hashCode() {
        long ht = this.getTime();
        return (int)ht ^ (int)(ht >> 32);
    }
    
    public String toString() {
        BaseCalendar$Date date = normalize();
        StringBuilder sb = new StringBuilder(28);
        int index = date.getDayOfWeek();
        if (index == gcal.SUNDAY) {
            index = 8;
        }
        convertToAbbr(sb, wtb[index]).append(' ');
        convertToAbbr(sb, wtb[date.getMonth() - 1 + 2 + 7]).append(' ');
        CalendarUtils.sprintf0d(sb, date.getDayOfMonth(), 2).append(' ');
        CalendarUtils.sprintf0d(sb, date.getHours(), 2).append(':');
        CalendarUtils.sprintf0d(sb, date.getMinutes(), 2).append(':');
        CalendarUtils.sprintf0d(sb, date.getSeconds(), 2).append(' ');
        TimeZone zi = date.getZone();
        if (zi != null) {
            sb.append(zi.getDisplayName(date.isDaylightTime(), zi.SHORT, Locale.US));
        } else {
            sb.append("GMT");
        }
        sb.append(' ').append(date.getYear());
        return sb.toString();
    }
    
    private static final StringBuilder convertToAbbr(StringBuilder sb, String name) {
        sb.append(Character.toUpperCase(name.charAt(0)));
        sb.append(name.charAt(1)).append(name.charAt(2));
        return sb;
    }
    
    
    public String toLocaleString() {
        DateFormat formatter = DateFormat.getDateTimeInstance();
        return formatter.format(this);
    }
    
    
    public String toGMTString() {
        long t = getTime();
        BaseCalendar cal = getCalendarSystem(t);
        BaseCalendar$Date date = (BaseCalendar$Date)(BaseCalendar$Date)cal.getCalendarDate(getTime(), (TimeZone)null);
        StringBuilder sb = new StringBuilder(32);
        CalendarUtils.sprintf0d(sb, date.getDayOfMonth(), 1).append(' ');
        convertToAbbr(sb, wtb[date.getMonth() - 1 + 2 + 7]).append(' ');
        sb.append(date.getYear()).append(' ');
        CalendarUtils.sprintf0d(sb, date.getHours(), 2).append(':');
        CalendarUtils.sprintf0d(sb, date.getMinutes(), 2).append(':');
        CalendarUtils.sprintf0d(sb, date.getSeconds(), 2);
        sb.append(" GMT");
        return sb.toString();
    }
    
    
    public int getTimezoneOffset() {
        int zoneOffset;
        if (cdate == null) {
            TimeZone tz = TimeZone.getDefaultRef();
            if (tz instanceof ZoneInfo) {
                zoneOffset = ((ZoneInfo)(ZoneInfo)tz).getOffsets(fastTime, null);
            } else {
                zoneOffset = tz.getOffset(fastTime);
            }
        } else {
            normalize();
            zoneOffset = cdate.getZoneOffset();
        }
        return -zoneOffset / 60000;
    }
    
    private final BaseCalendar$Date getCalendarDate() {
        if (cdate == null) {
            BaseCalendar cal = getCalendarSystem(fastTime);
            cdate = (BaseCalendar$Date)(BaseCalendar$Date)cal.getCalendarDate(fastTime, TimeZone.getDefaultRef());
        }
        return cdate;
    }
    
    private final BaseCalendar$Date normalize() {
        if (cdate == null) {
            BaseCalendar cal = getCalendarSystem(fastTime);
            cdate = (BaseCalendar$Date)(BaseCalendar$Date)cal.getCalendarDate(fastTime, TimeZone.getDefaultRef());
            return cdate;
        }
        if (!cdate.isNormalized()) {
            cdate = normalize(cdate);
        }
        TimeZone tz = TimeZone.getDefaultRef();
        if (tz != cdate.getZone()) {
            cdate.setZone(tz);
            CalendarSystem cal = getCalendarSystem(cdate);
            cal.getCalendarDate(fastTime, cdate);
        }
        return cdate;
    }
    
    private final BaseCalendar$Date normalize(BaseCalendar$Date date) {
        int y = date.getNormalizedYear();
        int m = date.getMonth();
        int d = date.getDayOfMonth();
        int hh = date.getHours();
        int mm = date.getMinutes();
        int ss = date.getSeconds();
        int ms = date.getMillis();
        TimeZone tz = date.getZone();
        if (y == 1582 || y > 280000000 || y < -280000000) {
            if (tz == null) {
                tz = TimeZone.getTimeZone("GMT");
            }
            GregorianCalendar gc = new GregorianCalendar(tz);
            gc.clear();
            gc.set(gc.MILLISECOND, ms);
            gc.set(y, m - 1, d, hh, mm, ss);
            fastTime = gc.getTimeInMillis();
            BaseCalendar cal = getCalendarSystem(fastTime);
            date = (BaseCalendar$Date)(BaseCalendar$Date)cal.getCalendarDate(fastTime, tz);
            return date;
        }
        BaseCalendar cal = getCalendarSystem(y);
        if (cal != getCalendarSystem(date)) {
            date = (BaseCalendar$Date)(BaseCalendar$Date)cal.newCalendarDate(tz);
            date.setNormalizedDate(y, m, d).setTimeOfDay(hh, mm, ss, ms);
        }
        fastTime = cal.getTime(date);
        BaseCalendar ncal = getCalendarSystem(fastTime);
        if (ncal != cal) {
            date = (BaseCalendar$Date)(BaseCalendar$Date)ncal.newCalendarDate(tz);
            date.setNormalizedDate(y, m, d).setTimeOfDay(hh, mm, ss, ms);
            fastTime = ncal.getTime(date);
        }
        return date;
    }
    
    private static final BaseCalendar getCalendarSystem(int year) {
        if (year >= 1582) {
            return gcal;
        }
        return getJulianCalendar();
    }
    
    private static final BaseCalendar getCalendarSystem(long t) {
        if (t >= GregorianCalendar.DEFAULT_GREGORIAN_CUTOVER) {
            return gcal;
        }
        return getJulianCalendar();
    }
    
    private static final BaseCalendar getCalendarSystem(BaseCalendar$Date cdate) {
        if (jcal == null) {
            return gcal;
        }
        if (cdate.getEra() != null) {
            return jcal;
        }
        return gcal;
    }
    
    private static final synchronized BaseCalendar getJulianCalendar() {
        if (jcal == null) {
            jcal = (BaseCalendar)(BaseCalendar)CalendarSystem.forName("julian");
        }
        return jcal;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.writeLong(getTimeImpl());
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        fastTime = s.readLong();
    }
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((Date)x0);
    }
}
