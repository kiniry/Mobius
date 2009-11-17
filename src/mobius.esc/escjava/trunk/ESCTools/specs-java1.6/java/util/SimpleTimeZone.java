package java.util;

import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.IOException;
import sun.util.calendar.CalendarSystem;
import sun.util.calendar.CalendarUtils;
import sun.util.calendar.BaseCalendar;
import sun.util.calendar.Gregorian;

public class SimpleTimeZone extends TimeZone {
    
    public SimpleTimeZone(int rawOffset, String ID) {
        
        this.rawOffset = rawOffset;
        setID(ID);
        dstSavings = millisPerHour;
    }
    
    public SimpleTimeZone(int rawOffset, String ID, int startMonth, int startDay, int startDayOfWeek, int startTime, int endMonth, int endDay, int endDayOfWeek, int endTime) {
        this(rawOffset, ID, startMonth, startDay, startDayOfWeek, startTime, WALL_TIME, endMonth, endDay, endDayOfWeek, endTime, WALL_TIME, millisPerHour);
    }
    
    public SimpleTimeZone(int rawOffset, String ID, int startMonth, int startDay, int startDayOfWeek, int startTime, int endMonth, int endDay, int endDayOfWeek, int endTime, int dstSavings) {
        this(rawOffset, ID, startMonth, startDay, startDayOfWeek, startTime, WALL_TIME, endMonth, endDay, endDayOfWeek, endTime, WALL_TIME, dstSavings);
    }
    
    public SimpleTimeZone(int rawOffset, String ID, int startMonth, int startDay, int startDayOfWeek, int startTime, int startTimeMode, int endMonth, int endDay, int endDayOfWeek, int endTime, int endTimeMode, int dstSavings) {
        
        setID(ID);
        this.rawOffset = rawOffset;
        this.startMonth = startMonth;
        this.startDay = startDay;
        this.startDayOfWeek = startDayOfWeek;
        this.startTime = startTime;
        this.startTimeMode = startTimeMode;
        this.endMonth = endMonth;
        this.endDay = endDay;
        this.endDayOfWeek = endDayOfWeek;
        this.endTime = endTime;
        this.endTimeMode = endTimeMode;
        this.dstSavings = dstSavings;
        decodeRules();
        if (dstSavings <= 0) {
            throw new IllegalArgumentException("Illegal daylight saving value: " + dstSavings);
        }
    }
    
    public void setStartYear(int year) {
        startYear = year;
        invalidateCache();
    }
    
    public void setStartRule(int startMonth, int startDay, int startDayOfWeek, int startTime) {
        this.startMonth = startMonth;
        this.startDay = startDay;
        this.startDayOfWeek = startDayOfWeek;
        this.startTime = startTime;
        startTimeMode = WALL_TIME;
        decodeStartRule();
        invalidateCache();
    }
    
    public void setStartRule(int startMonth, int startDay, int startTime) {
        setStartRule(startMonth, startDay, 0, startTime);
    }
    
    public void setStartRule(int startMonth, int startDay, int startDayOfWeek, int startTime, boolean after) {
        if (after) {
            setStartRule(startMonth, startDay, -startDayOfWeek, startTime);
        } else {
            setStartRule(startMonth, -startDay, -startDayOfWeek, startTime);
        }
    }
    
    public void setEndRule(int endMonth, int endDay, int endDayOfWeek, int endTime) {
        this.endMonth = endMonth;
        this.endDay = endDay;
        this.endDayOfWeek = endDayOfWeek;
        this.endTime = endTime;
        this.endTimeMode = WALL_TIME;
        decodeEndRule();
        invalidateCache();
    }
    
    public void setEndRule(int endMonth, int endDay, int endTime) {
        setEndRule(endMonth, endDay, 0, endTime);
    }
    
    public void setEndRule(int endMonth, int endDay, int endDayOfWeek, int endTime, boolean after) {
        if (after) {
            setEndRule(endMonth, endDay, -endDayOfWeek, endTime);
        } else {
            setEndRule(endMonth, -endDay, -endDayOfWeek, endTime);
        }
    }
    
    public int getOffset(long date) {
        return getOffsets(date, null);
    }
    
    int getOffsets(long date, int[] offsets) {
        int offset = rawOffset;
        computeOffset: if (useDaylight) {
            synchronized (this) {
                if (cacheStart != 0) {
                    if (date >= cacheStart && date < cacheEnd) {
                        offset += dstSavings;
                        break computeOffset;
                    }
                }
            }
            BaseCalendar cal = date >= GregorianCalendar.DEFAULT_GREGORIAN_CUTOVER ? gcal : (BaseCalendar)(BaseCalendar)CalendarSystem.forName("julian");
            BaseCalendar$Date cdate = (BaseCalendar$Date)(BaseCalendar$Date)cal.newCalendarDate(TimeZone.NO_TIMEZONE);
            cal.getCalendarDate(date + rawOffset, cdate);
            int year = cdate.getNormalizedYear();
            if (year >= startYear) {
                cdate.setTimeOfDay(0, 0, 0, 0);
                offset = getOffset(cal, cdate, year, date);
            }
        }
        if (offsets != null) {
            offsets[0] = rawOffset;
            offsets[1] = offset - rawOffset;
        }
        return offset;
    }
    
    public int getOffset(int era, int year, int month, int day, int dayOfWeek, int millis) {
        if (era != GregorianCalendar.AD && era != GregorianCalendar.BC) {
            throw new IllegalArgumentException("Illegal era " + era);
        }
        int y = year;
        if (era == GregorianCalendar.BC) {
            y = 1 - y;
        }
        if (y >= 292278994) {
            y = 2800 + y % 2800;
        } else if (y <= -292269054) {
            y = (int)CalendarUtils.mod((long)y, 28);
        }
        int m = month + 1;
        BaseCalendar cal = gcal;
        BaseCalendar$Date cdate = (BaseCalendar$Date)(BaseCalendar$Date)cal.newCalendarDate(TimeZone.NO_TIMEZONE);
        cdate.setDate(y, m, day);
        long time = cal.getTime(cdate);
        time += millis - rawOffset;
        if (time < GregorianCalendar.DEFAULT_GREGORIAN_CUTOVER) {
            cal = (BaseCalendar)(BaseCalendar)CalendarSystem.forName("julian");
            cdate = (BaseCalendar$Date)(BaseCalendar$Date)cal.newCalendarDate(TimeZone.NO_TIMEZONE);
            cdate.setNormalizedDate(y, m, day);
            time = cal.getTime(cdate) + millis - rawOffset;
        }
        if ((cdate.getNormalizedYear() != y) || (cdate.getMonth() != m) || (cdate.getDayOfMonth() != day) || (dayOfWeek < Calendar.SUNDAY || dayOfWeek > Calendar.SATURDAY) || (millis < 0 || millis >= (24 * 60 * 60 * 1000))) {
            throw new IllegalArgumentException();
        }
        if (!useDaylight || year < startYear || era != GregorianCalendar.CE) {
            return rawOffset;
        }
        return getOffset(cal, cdate, y, time);
    }
    
    private int getOffset(BaseCalendar cal, BaseCalendar$Date cdate, int year, long time) {
        synchronized (this) {
            if (cacheStart != 0) {
                if (time >= cacheStart && time < cacheEnd) {
                    return rawOffset + dstSavings;
                }
                if (year == cacheYear) {
                    return rawOffset;
                }
            }
        }
        long start = getStart(cal, cdate, year);
        long end = getEnd(cal, cdate, year);
        int offset = rawOffset;
        if (start <= end) {
            if (time >= start && time < end) {
                offset += dstSavings;
            }
            synchronized (this) {
                cacheYear = year;
                cacheStart = start;
                cacheEnd = end;
            }
        } else {
            if (time < end) {
                start = getStart(cal, cdate, year - 1);
                if (time >= start) {
                    offset += dstSavings;
                }
            } else if (time >= start) {
                end = getEnd(cal, cdate, year + 1);
                if (time < end) {
                    offset += dstSavings;
                }
            }
            if (start <= end) {
                synchronized (this) {
                    cacheYear = (long)startYear - 1;
                    cacheStart = start;
                    cacheEnd = end;
                }
            }
        }
        return offset;
    }
    
    private long getStart(BaseCalendar cal, BaseCalendar$Date cdate, int year) {
        int time = startTime;
        if (startTimeMode != UTC_TIME) {
            time -= rawOffset;
        }
        return getTransition(cal, cdate, startMode, year, startMonth, startDay, startDayOfWeek, time);
    }
    
    private long getEnd(BaseCalendar cal, BaseCalendar$Date cdate, int year) {
        int time = endTime;
        if (startTimeMode != UTC_TIME) {
            time -= rawOffset;
        }
        if (startTimeMode == WALL_TIME) {
            time -= dstSavings;
        }
        return getTransition(cal, cdate, endMode, year, endMonth, endDay, endDayOfWeek, time);
    }
    
    private long getTransition(BaseCalendar cal, BaseCalendar$Date cdate, int mode, int year, int month, int dayOfMonth, int dayOfWeek, int timeOfDay) {
        cdate.setNormalizedYear(year);
        cdate.setMonth(month + 1);
        switch (mode) {
        case DOM_MODE: 
            cdate.setDayOfMonth(dayOfMonth);
            break;
        
        case DOW_IN_MONTH_MODE: 
            cdate.setDayOfMonth(1);
            if (dayOfMonth < 0) {
                cdate.setDayOfMonth(cal.getMonthLength(cdate));
            }
            cdate = (BaseCalendar$Date)(BaseCalendar$Date)cal.getNthDayOfWeek(dayOfMonth, dayOfWeek, cdate);
            break;
        
        case DOW_GE_DOM_MODE: 
            cdate.setDayOfMonth(dayOfMonth);
            cdate = (BaseCalendar$Date)(BaseCalendar$Date)cal.getNthDayOfWeek(1, dayOfWeek, cdate);
            break;
        
        case DOW_LE_DOM_MODE: 
            cdate.setDayOfMonth(dayOfMonth);
            cdate = (BaseCalendar$Date)(BaseCalendar$Date)cal.getNthDayOfWeek(-1, dayOfWeek, cdate);
            break;
        
        }
        return cal.getTime(cdate) + timeOfDay;
    }
    
    public int getRawOffset() {
        return rawOffset;
    }
    
    public void setRawOffset(int offsetMillis) {
        this.rawOffset = offsetMillis;
    }
    
    public void setDSTSavings(int millisSavedDuringDST) {
        if (millisSavedDuringDST <= 0) {
            throw new IllegalArgumentException("Illegal daylight saving value: " + millisSavedDuringDST);
        }
        dstSavings = millisSavedDuringDST;
    }
    
    public int getDSTSavings() {
        if (useDaylight) {
            return dstSavings;
        }
        return 0;
    }
    
    public boolean useDaylightTime() {
        return useDaylight;
    }
    
    public boolean inDaylightTime(Date date) {
        return (getOffset(date.getTime()) != rawOffset);
    }
    
    public Object clone() {
        return super.clone();
    }
    
    public synchronized int hashCode() {
        return startMonth ^ startDay ^ startDayOfWeek ^ startTime ^ endMonth ^ endDay ^ endDayOfWeek ^ endTime ^ rawOffset;
    }
    
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (!(obj instanceof SimpleTimeZone)) {
            return false;
        }
        SimpleTimeZone that = (SimpleTimeZone)(SimpleTimeZone)obj;
        return getID().equals(that.getID()) && hasSameRules(that);
    }
    
    public boolean hasSameRules(TimeZone other) {
        if (this == other) {
            return true;
        }
        if (!(other instanceof SimpleTimeZone)) {
            return false;
        }
        SimpleTimeZone that = (SimpleTimeZone)(SimpleTimeZone)other;
        return rawOffset == that.rawOffset && useDaylight == that.useDaylight && (!useDaylight || (dstSavings == that.dstSavings && startMode == that.startMode && startMonth == that.startMonth && startDay == that.startDay && startDayOfWeek == that.startDayOfWeek && startTime == that.startTime && startTimeMode == that.startTimeMode && endMode == that.endMode && endMonth == that.endMonth && endDay == that.endDay && endDayOfWeek == that.endDayOfWeek && endTime == that.endTime && endTimeMode == that.endTimeMode && startYear == that.startYear));
    }
    
    public String toString() {
        return getClass().getName() + "[id=" + getID() + ",offset=" + rawOffset + ",dstSavings=" + dstSavings + ",useDaylight=" + useDaylight + ",startYear=" + startYear + ",startMode=" + startMode + ",startMonth=" + startMonth + ",startDay=" + startDay + ",startDayOfWeek=" + startDayOfWeek + ",startTime=" + startTime + ",startTimeMode=" + startTimeMode + ",endMode=" + endMode + ",endMonth=" + endMonth + ",endDay=" + endDay + ",endDayOfWeek=" + endDayOfWeek + ",endTime=" + endTime + ",endTimeMode=" + endTimeMode + ']';
    }
    private int startMonth;
    private int startDay;
    private int startDayOfWeek;
    private int startTime;
    private int startTimeMode;
    private int endMonth;
    private int endDay;
    private int endDayOfWeek;
    private int endTime;
    private int endTimeMode;
    private int startYear;
    private int rawOffset;
    private boolean useDaylight = false;
    private static final int millisPerHour = 60 * 60 * 1000;
    private static final int millisPerDay = 24 * millisPerHour;
    private final byte[] monthLength = staticMonthLength;
    private static final byte[] staticMonthLength = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
    private static final byte[] staticLeapMonthLength = {31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
    private int startMode;
    private int endMode;
    private int dstSavings;
    private static final Gregorian gcal = CalendarSystem.getGregorianCalendar();
    private transient long cacheYear;
    private transient long cacheStart;
    private transient long cacheEnd;
    private static final int DOM_MODE = 1;
    private static final int DOW_IN_MONTH_MODE = 2;
    private static final int DOW_GE_DOM_MODE = 3;
    private static final int DOW_LE_DOM_MODE = 4;
    public static final int WALL_TIME = 0;
    public static final int STANDARD_TIME = 1;
    public static final int UTC_TIME = 2;
    static final long serialVersionUID = -403250971215465050L;
    static final int currentSerialVersion = 2;
    private int serialVersionOnStream = currentSerialVersion;
    
    private synchronized void invalidateCache() {
        cacheYear = startYear - 1;
        cacheStart = cacheEnd = 0;
    }
    
    private void decodeRules() {
        decodeStartRule();
        decodeEndRule();
    }
    
    private void decodeStartRule() {
        useDaylight = (startDay != 0) && (endDay != 0);
        if (startDay != 0) {
            if (startMonth < Calendar.JANUARY || startMonth > Calendar.DECEMBER) {
                throw new IllegalArgumentException("Illegal start month " + startMonth);
            }
            if (startTime < 0 || startTime >= millisPerDay) {
                throw new IllegalArgumentException("Illegal start time " + startTime);
            }
            if (startDayOfWeek == 0) {
                startMode = DOM_MODE;
            } else {
                if (startDayOfWeek > 0) {
                    startMode = DOW_IN_MONTH_MODE;
                } else {
                    startDayOfWeek = -startDayOfWeek;
                    if (startDay > 0) {
                        startMode = DOW_GE_DOM_MODE;
                    } else {
                        startDay = -startDay;
                        startMode = DOW_LE_DOM_MODE;
                    }
                }
                if (startDayOfWeek > Calendar.SATURDAY) {
                    throw new IllegalArgumentException("Illegal start day of week " + startDayOfWeek);
                }
            }
            if (startMode == DOW_IN_MONTH_MODE) {
                if (startDay < -5 || startDay > 5) {
                    throw new IllegalArgumentException("Illegal start day of week in month " + startDay);
                }
            } else if (startDay < 1 || startDay > staticMonthLength[startMonth]) {
                throw new IllegalArgumentException("Illegal start day " + startDay);
            }
        }
    }
    
    private void decodeEndRule() {
        useDaylight = (startDay != 0) && (endDay != 0);
        if (endDay != 0) {
            if (endMonth < Calendar.JANUARY || endMonth > Calendar.DECEMBER) {
                throw new IllegalArgumentException("Illegal end month " + endMonth);
            }
            if (endTime < 0 || endTime >= millisPerDay) {
                throw new IllegalArgumentException("Illegal end time " + endTime);
            }
            if (endDayOfWeek == 0) {
                endMode = DOM_MODE;
            } else {
                if (endDayOfWeek > 0) {
                    endMode = DOW_IN_MONTH_MODE;
                } else {
                    endDayOfWeek = -endDayOfWeek;
                    if (endDay > 0) {
                        endMode = DOW_GE_DOM_MODE;
                    } else {
                        endDay = -endDay;
                        endMode = DOW_LE_DOM_MODE;
                    }
                }
                if (endDayOfWeek > Calendar.SATURDAY) {
                    throw new IllegalArgumentException("Illegal end day of week " + endDayOfWeek);
                }
            }
            if (endMode == DOW_IN_MONTH_MODE) {
                if (endDay < -5 || endDay > 5) {
                    throw new IllegalArgumentException("Illegal end day of week in month " + endDay);
                }
            } else if (endDay < 1 || endDay > staticMonthLength[endMonth]) {
                throw new IllegalArgumentException("Illegal end day " + endDay);
            }
        }
    }
    
    private void makeRulesCompatible() {
        switch (startMode) {
        case DOM_MODE: 
            startDay = 1 + (startDay / 7);
            startDayOfWeek = Calendar.SUNDAY;
            break;
        
        case DOW_GE_DOM_MODE: 
            if (startDay != 1) {
                startDay = 1 + (startDay / 7);
            }
            break;
        
        case DOW_LE_DOM_MODE: 
            if (startDay >= 30) {
                startDay = -1;
            } else {
                startDay = 1 + (startDay / 7);
            }
            break;
        
        }
        switch (endMode) {
        case DOM_MODE: 
            endDay = 1 + (endDay / 7);
            endDayOfWeek = Calendar.SUNDAY;
            break;
        
        case DOW_GE_DOM_MODE: 
            if (endDay != 1) {
                endDay = 1 + (endDay / 7);
            }
            break;
        
        case DOW_LE_DOM_MODE: 
            if (endDay >= 30) {
                endDay = -1;
            } else {
                endDay = 1 + (endDay / 7);
            }
            break;
        
        }
        switch (startTimeMode) {
        case UTC_TIME: 
            startTime += rawOffset;
            break;
        
        }
        while (startTime < 0) {
            startTime += millisPerDay;
            startDayOfWeek = 1 + ((startDayOfWeek + 5) % 7);
        }
        while (startTime >= millisPerDay) {
            startTime -= millisPerDay;
            startDayOfWeek = 1 + (startDayOfWeek % 7);
        }
        switch (endTimeMode) {
        case UTC_TIME: 
            endTime += rawOffset + dstSavings;
            break;
        
        case STANDARD_TIME: 
            endTime += dstSavings;
        
        }
        while (endTime < 0) {
            endTime += millisPerDay;
            endDayOfWeek = 1 + ((endDayOfWeek + 5) % 7);
        }
        while (endTime >= millisPerDay) {
            endTime -= millisPerDay;
            endDayOfWeek = 1 + (endDayOfWeek % 7);
        }
    }
    
    private byte[] packRules() {
        byte[] rules = new byte[6];
        rules[0] = (byte)startDay;
        rules[1] = (byte)startDayOfWeek;
        rules[2] = (byte)endDay;
        rules[3] = (byte)endDayOfWeek;
        rules[4] = (byte)startTimeMode;
        rules[5] = (byte)endTimeMode;
        return rules;
    }
    
    private void unpackRules(byte[] rules) {
        startDay = rules[0];
        startDayOfWeek = rules[1];
        endDay = rules[2];
        endDayOfWeek = rules[3];
        if (rules.length >= 6) {
            startTimeMode = rules[4];
            endTimeMode = rules[5];
        }
    }
    
    private int[] packTimes() {
        int[] times = new int[2];
        times[0] = startTime;
        times[1] = endTime;
        return times;
    }
    
    private void unpackTimes(int[] times) {
        startTime = times[0];
        endTime = times[1];
    }
    
    private void writeObject(ObjectOutputStream stream) throws IOException {
        byte[] rules = packRules();
        int[] times = packTimes();
        makeRulesCompatible();
        stream.defaultWriteObject();
        stream.writeInt(rules.length);
        stream.write(rules);
        stream.writeObject(times);
        unpackRules(rules);
        unpackTimes(times);
    }
    
    private void readObject(ObjectInputStream stream) throws IOException, ClassNotFoundException {
        stream.defaultReadObject();
        if (serialVersionOnStream < 1) {
            if (startDayOfWeek == 0) {
                startDayOfWeek = Calendar.SUNDAY;
            }
            if (endDayOfWeek == 0) {
                endDayOfWeek = Calendar.SUNDAY;
            }
            startMode = endMode = DOW_IN_MONTH_MODE;
            dstSavings = millisPerHour;
        } else {
            int length = stream.readInt();
            byte[] rules = new byte[length];
            stream.readFully(rules);
            unpackRules(rules);
        }
        if (serialVersionOnStream >= 2) {
            int[] times = (int[])(int[])stream.readObject();
            unpackTimes(times);
        }
        serialVersionOnStream = currentSerialVersion;
    }
}
