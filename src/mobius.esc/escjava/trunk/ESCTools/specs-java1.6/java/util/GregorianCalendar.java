package java.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import sun.util.calendar.BaseCalendar;
import sun.util.calendar.CalendarDate;
import sun.util.calendar.CalendarSystem;
import sun.util.calendar.CalendarUtils;
import sun.util.calendar.Era;
import sun.util.calendar.Gregorian;
import sun.util.calendar.JulianCalendar;
import sun.util.calendar.ZoneInfo;

public class GregorianCalendar extends Calendar {
    /*synthetic*/ static final boolean $assertionsDisabled = !GregorianCalendar.class.desiredAssertionStatus();
    public static final int BC = 0;
    static final int BCE = 0;
    public static final int AD = 1;
    static final int CE = 1;
    private static final int EPOCH_OFFSET = 719163;
    private static final int EPOCH_YEAR = 1970;
    static final int[] MONTH_LENGTH = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
    static final int[] LEAP_MONTH_LENGTH = {31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
    private static final int ONE_SECOND = 1000;
    private static final int ONE_MINUTE = 60 * ONE_SECOND;
    private static final int ONE_HOUR = 60 * ONE_MINUTE;
    private static final long ONE_DAY = 24 * ONE_HOUR;
    private static final long ONE_WEEK = 7 * ONE_DAY;
    static final int[] MIN_VALUES = {BCE, 1, JANUARY, 1, 0, 1, 1, SUNDAY, 1, AM, 0, 0, 0, 0, 0, -13 * ONE_HOUR, 0};
    static final int[] LEAST_MAX_VALUES = {CE, 292269054, DECEMBER, 52, 4, 28, 365, SATURDAY, 4, PM, 11, 23, 59, 59, 999, 14 * ONE_HOUR, 20 * ONE_MINUTE};
    static final int[] MAX_VALUES = {CE, 292278994, DECEMBER, 53, 6, 31, 366, SATURDAY, 6, PM, 11, 23, 59, 59, 999, 14 * ONE_HOUR, 2 * ONE_HOUR};
    static final long serialVersionUID = -8125100834729963327L;
    private static final Gregorian gcal = CalendarSystem.getGregorianCalendar();
    private static JulianCalendar jcal;
    private static Era[] jeras;
    static final long DEFAULT_GREGORIAN_CUTOVER = -12219292800000L;
    private long gregorianCutover = DEFAULT_GREGORIAN_CUTOVER;
    private transient long gregorianCutoverDate = (((DEFAULT_GREGORIAN_CUTOVER + 1) / ONE_DAY) - 1) + EPOCH_OFFSET;
    private transient int gregorianCutoverYear = 1582;
    private transient int gregorianCutoverYearJulian = 1582;
    private transient BaseCalendar$Date gdate;
    private transient BaseCalendar$Date cdate;
    private transient BaseCalendar calsys;
    private transient int[] zoneOffsets;
    private transient int[] originalFields;
    
    public GregorianCalendar() {
        this(TimeZone.getDefaultRef(), Locale.getDefault());
        setZoneShared(true);
    }
    
    public GregorianCalendar(TimeZone zone) {
        this(zone, Locale.getDefault());
    }
    
    public GregorianCalendar(Locale aLocale) {
        this(TimeZone.getDefaultRef(), aLocale);
        setZoneShared(true);
    }
    
    public GregorianCalendar(TimeZone zone, Locale aLocale) {
        super(zone, aLocale);
        gdate = (BaseCalendar$Date)(BaseCalendar$Date)gcal.newCalendarDate(zone);
        setTimeInMillis(System.currentTimeMillis());
    }
    
    public GregorianCalendar(int year, int month, int dayOfMonth) {
        this(year, month, dayOfMonth, 0, 0, 0, 0);
    }
    
    public GregorianCalendar(int year, int month, int dayOfMonth, int hourOfDay, int minute) {
        this(year, month, dayOfMonth, hourOfDay, minute, 0, 0);
    }
    
    public GregorianCalendar(int year, int month, int dayOfMonth, int hourOfDay, int minute, int second) {
        this(year, month, dayOfMonth, hourOfDay, minute, second, 0);
    }
    
    GregorianCalendar(int year, int month, int dayOfMonth, int hourOfDay, int minute, int second, int millis) {
        
        gdate = (BaseCalendar$Date)(BaseCalendar$Date)gcal.newCalendarDate(getZone());
        this.set(YEAR, year);
        this.set(MONTH, month);
        this.set(DAY_OF_MONTH, dayOfMonth);
        if (hourOfDay >= 12 && hourOfDay <= 23) {
            this.internalSet(AM_PM, PM);
            this.internalSet(HOUR, hourOfDay - 12);
        } else {
            this.internalSet(HOUR, hourOfDay);
        }
        setFieldsComputed(HOUR_MASK | AM_PM_MASK);
        this.set(HOUR_OF_DAY, hourOfDay);
        this.set(MINUTE, minute);
        this.set(SECOND, second);
        this.internalSet(MILLISECOND, millis);
    }
    
    public void setGregorianChange(Date date) {
        long cutoverTime = date.getTime();
        if (cutoverTime == gregorianCutover) {
            return;
        }
        complete();
        setGregorianChange(cutoverTime);
    }
    
    private void setGregorianChange(long cutoverTime) {
        gregorianCutover = cutoverTime;
        gregorianCutoverDate = CalendarUtils.floorDivide(cutoverTime, ONE_DAY) + EPOCH_OFFSET;
        if (cutoverTime == Long.MAX_VALUE) {
            gregorianCutoverDate++;
        }
        BaseCalendar$Date d = getGregorianCutoverDate();
        gregorianCutoverYear = d.getYear();
        BaseCalendar jcal = getJulianCalendarSystem();
        d = (BaseCalendar$Date)(BaseCalendar$Date)jcal.newCalendarDate(TimeZone.NO_TIMEZONE);
        jcal.getCalendarDateFromFixedDate(d, gregorianCutoverDate - 1);
        gregorianCutoverYearJulian = d.getNormalizedYear();
        if (time < gregorianCutover) {
            setUnnormalized();
        }
    }
    
    public final Date getGregorianChange() {
        return new Date(gregorianCutover);
    }
    
    public boolean isLeapYear(int year) {
        if ((year & 3) != 0) {
            return false;
        }
        if (year > gregorianCutoverYear) {
            return (year % 100 != 0) || (year % 400 == 0);
        }
        if (year < gregorianCutoverYearJulian) {
            return true;
        }
        boolean gregorian;
        if (gregorianCutoverYear == gregorianCutoverYearJulian) {
            BaseCalendar$Date d = getCalendarDate(gregorianCutoverDate);
            gregorian = d.getMonth() < BaseCalendar.MARCH;
        } else {
            gregorian = year == gregorianCutoverYear;
        }
        return gregorian ? (year % 100 != 0) || (year % 400 == 0) : true;
    }
    
    public boolean equals(Object obj) {
        return obj instanceof GregorianCalendar && super.equals(obj) && gregorianCutover == ((GregorianCalendar)(GregorianCalendar)obj).gregorianCutover;
    }
    
    public int hashCode() {
        return super.hashCode() ^ (int)gregorianCutoverDate;
    }
    
    public void add(int field, int amount) {
        if (amount == 0) {
            return;
        }
        if (field < 0 || field >= ZONE_OFFSET) {
            throw new IllegalArgumentException();
        }
        complete();
        if (field == YEAR) {
            int year = internalGet(YEAR);
            if (internalGetEra() == CE) {
                year += amount;
                if (year > 0) {
                    set(YEAR, year);
                } else {
                    set(YEAR, 1 - year);
                    set(ERA, BCE);
                }
            } else {
                year -= amount;
                if (year > 0) {
                    set(YEAR, year);
                } else {
                    set(YEAR, 1 - year);
                    set(ERA, CE);
                }
            }
            pinDayOfMonth();
        } else if (field == MONTH) {
            int month = internalGet(MONTH) + amount;
            int year = internalGet(YEAR);
            int y_amount;
            if (month >= 0) {
                y_amount = month / 12;
            } else {
                y_amount = (month + 1) / 12 - 1;
            }
            if (y_amount != 0) {
                if (internalGetEra() == CE) {
                    year += y_amount;
                    if (year > 0) {
                        set(YEAR, year);
                    } else {
                        set(YEAR, 1 - year);
                        set(ERA, BCE);
                    }
                } else {
                    year -= y_amount;
                    if (year > 0) {
                        set(YEAR, year);
                    } else {
                        set(YEAR, 1 - year);
                        set(ERA, CE);
                    }
                }
            }
            if (month >= 0) {
                set(MONTH, (int)(month % 12));
            } else {
                month %= 12;
                if (month < 0) {
                    month += 12;
                }
                set(MONTH, JANUARY + month);
            }
            pinDayOfMonth();
        } else if (field == ERA) {
            int era = internalGet(ERA) + amount;
            if (era < 0) {
                era = 0;
            }
            if (era > 1) {
                era = 1;
            }
            set(ERA, era);
        } else {
            long delta = amount;
            long timeOfDay = 0;
            switch (field) {
            case HOUR: 
            
            case HOUR_OF_DAY: 
                delta *= 60 * 60 * 1000;
                break;
            
            case MINUTE: 
                delta *= 60 * 1000;
                break;
            
            case SECOND: 
                delta *= 1000;
                break;
            
            case MILLISECOND: 
                break;
            
            case WEEK_OF_YEAR: 
            
            case WEEK_OF_MONTH: 
            
            case DAY_OF_WEEK_IN_MONTH: 
                delta *= 7;
                break;
            
            case DAY_OF_MONTH: 
            
            case DAY_OF_YEAR: 
            
            case DAY_OF_WEEK: 
                break;
            
            case AM_PM: 
                delta = amount / 2;
                timeOfDay = 12 * (amount % 2);
                break;
            
            }
            if (field >= HOUR) {
                setTimeInMillis(time + delta);
                return;
            }
            long fd = getCurrentFixedDate();
            timeOfDay += internalGet(HOUR_OF_DAY);
            timeOfDay *= 60;
            timeOfDay += internalGet(MINUTE);
            timeOfDay *= 60;
            timeOfDay += internalGet(SECOND);
            timeOfDay *= 1000;
            timeOfDay += internalGet(MILLISECOND);
            if (timeOfDay >= ONE_DAY) {
                fd++;
                timeOfDay -= ONE_DAY;
            } else if (timeOfDay < 0) {
                fd--;
                timeOfDay += ONE_DAY;
            }
            fd += delta;
            int zoneOffset = internalGet(ZONE_OFFSET) + internalGet(DST_OFFSET);
            setTimeInMillis((fd - EPOCH_OFFSET) * ONE_DAY + timeOfDay - zoneOffset);
            zoneOffset -= internalGet(ZONE_OFFSET) + internalGet(DST_OFFSET);
            if (zoneOffset != 0) {
                setTimeInMillis(time + zoneOffset);
                long fd2 = getCurrentFixedDate();
                if (fd2 != fd) {
                    setTimeInMillis(time - zoneOffset);
                }
            }
        }
    }
    
    public void roll(int field, boolean up) {
        roll(field, up ? +1 : -1);
    }
    
    public void roll(int field, int amount) {
        if (amount == 0) {
            return;
        }
        if (field < 0 || field >= ZONE_OFFSET) {
            throw new IllegalArgumentException();
        }
        complete();
        int min = getMinimum(field);
        int max = getMaximum(field);
        switch (field) {
        case AM_PM: 
        
        case ERA: 
        
        case YEAR: 
        
        case MINUTE: 
        
        case SECOND: 
        
        case MILLISECOND: 
            break;
        
        case HOUR: 
        
        case HOUR_OF_DAY: 
            {
                int unit = max + 1;
                int h = internalGet(field);
                int nh = (h + amount) % unit;
                if (nh < 0) {
                    nh += unit;
                }
                time += ONE_HOUR * (nh - h);
                CalendarDate d = calsys.getCalendarDate(time, getZone());
                if (internalGet(DAY_OF_MONTH) != d.getDayOfMonth()) {
                    d.setDate(internalGet(YEAR), internalGet(MONTH) + 1, internalGet(DAY_OF_MONTH));
                    if (field == HOUR) {
                        if (!$assertionsDisabled && !(internalGet(AM_PM) == PM)) throw new AssertionError();
                        d.addHours(+12);
                    }
                    time = calsys.getTime(d);
                }
                int hourOfDay = d.getHours();
                internalSet(field, hourOfDay % unit);
                if (field == HOUR) {
                    internalSet(HOUR_OF_DAY, hourOfDay);
                } else {
                    internalSet(AM_PM, hourOfDay / 12);
                    internalSet(HOUR, hourOfDay % 12);
                }
                int zoneOffset = d.getZoneOffset();
                int saving = d.getDaylightSaving();
                internalSet(ZONE_OFFSET, zoneOffset - saving);
                internalSet(DST_OFFSET, saving);
                return;
            }
        
        case MONTH: 
            {
                if (!isCutoverYear(cdate.getNormalizedYear())) {
                    int mon = (internalGet(MONTH) + amount) % 12;
                    if (mon < 0) {
                        mon += 12;
                    }
                    set(MONTH, mon);
                    int monthLen = monthLength(mon);
                    if (internalGet(DAY_OF_MONTH) > monthLen) {
                        set(DAY_OF_MONTH, monthLen);
                    }
                } else {
                    int yearLength = getActualMaximum(MONTH) + 1;
                    int mon = (internalGet(MONTH) + amount) % yearLength;
                    if (mon < 0) {
                        mon += yearLength;
                    }
                    set(MONTH, mon);
                    int monthLen = getActualMaximum(DAY_OF_MONTH);
                    if (internalGet(DAY_OF_MONTH) > monthLen) {
                        set(DAY_OF_MONTH, monthLen);
                    }
                }
                return;
            }
        
        case WEEK_OF_YEAR: 
            {
                int y = cdate.getNormalizedYear();
                max = getActualMaximum(WEEK_OF_YEAR);
                set(DAY_OF_WEEK, internalGet(DAY_OF_WEEK));
                int woy = internalGet(WEEK_OF_YEAR);
                int value = woy + amount;
                if (!isCutoverYear(y)) {
                    if (value > min && value < max) {
                        set(WEEK_OF_YEAR, value);
                        return;
                    }
                    long fd = getCurrentFixedDate();
                    long day1 = fd - (7 * (woy - min));
                    if (calsys.getYearFromFixedDate(day1) != y) {
                        min++;
                    }
                    fd += 7 * (max - internalGet(WEEK_OF_YEAR));
                    if (calsys.getYearFromFixedDate(fd) != y) {
                        max--;
                    }
                    break;
                }
                long fd = getCurrentFixedDate();
                BaseCalendar cal;
                if (gregorianCutoverYear == gregorianCutoverYearJulian) {
                    cal = getCutoverCalendarSystem();
                } else if (y == gregorianCutoverYear) {
                    cal = gcal;
                } else {
                    cal = getJulianCalendarSystem();
                }
                long day1 = fd - (7 * (woy - min));
                if (cal.getYearFromFixedDate(day1) != y) {
                    min++;
                }
                fd += 7 * (max - woy);
                cal = (fd >= gregorianCutoverDate) ? gcal : getJulianCalendarSystem();
                if (cal.getYearFromFixedDate(fd) != y) {
                    max--;
                }
                value = getRolledValue(woy, amount, min, max) - 1;
                BaseCalendar$Date d = getCalendarDate(day1 + value * 7);
                set(MONTH, d.getMonth() - 1);
                set(DAY_OF_MONTH, d.getDayOfMonth());
                return;
            }
        
        case WEEK_OF_MONTH: 
            {
                boolean isCutoverYear = isCutoverYear(cdate.getNormalizedYear());
                int dow = internalGet(DAY_OF_WEEK) - getFirstDayOfWeek();
                if (dow < 0) {
                    dow += 7;
                }
                long fd = getCurrentFixedDate();
                long month1;
                int monthLength;
                if (isCutoverYear) {
                    month1 = getFixedDateMonth1(cdate, fd);
                    monthLength = actualMonthLength();
                } else {
                    month1 = fd - internalGet(DAY_OF_MONTH) + 1;
                    monthLength = calsys.getMonthLength(cdate);
                }
                long monthDay1st = calsys.getDayOfWeekDateOnOrBefore(month1 + 6, getFirstDayOfWeek());
                if ((int)(monthDay1st - month1) >= getMinimalDaysInFirstWeek()) {
                    monthDay1st -= 7;
                }
                max = getActualMaximum(field);
                int value = getRolledValue(internalGet(field), amount, 1, max) - 1;
                long nfd = monthDay1st + value * 7 + dow;
                if (nfd < month1) {
                    nfd = month1;
                } else if (nfd >= (month1 + monthLength)) {
                    nfd = month1 + monthLength - 1;
                }
                int dayOfMonth;
                if (isCutoverYear) {
                    BaseCalendar$Date d = getCalendarDate(nfd);
                    dayOfMonth = d.getDayOfMonth();
                } else {
                    dayOfMonth = (int)(nfd - month1) + 1;
                }
                set(DAY_OF_MONTH, dayOfMonth);
                return;
            }
        
        case DAY_OF_MONTH: 
            {
                if (!isCutoverYear(cdate.getNormalizedYear())) {
                    max = calsys.getMonthLength(cdate);
                    break;
                }
                long fd = getCurrentFixedDate();
                long month1 = getFixedDateMonth1(cdate, fd);
                int value = getRolledValue((int)(fd - month1), amount, 0, actualMonthLength() - 1);
                BaseCalendar$Date d = getCalendarDate(month1 + value);
                if (!$assertionsDisabled && !(d.getMonth() - 1 == internalGet(MONTH))) throw new AssertionError();
                set(DAY_OF_MONTH, d.getDayOfMonth());
                return;
            }
        
        case DAY_OF_YEAR: 
            {
                max = getActualMaximum(field);
                if (!isCutoverYear(cdate.getNormalizedYear())) {
                    break;
                }
                long fd = getCurrentFixedDate();
                long jan1 = fd - internalGet(DAY_OF_YEAR) + 1;
                int value = getRolledValue((int)(fd - jan1) + 1, amount, min, max);
                BaseCalendar$Date d = getCalendarDate(jan1 + value - 1);
                set(MONTH, d.getMonth() - 1);
                set(DAY_OF_MONTH, d.getDayOfMonth());
                return;
            }
        
        case DAY_OF_WEEK: 
            {
                if (!isCutoverYear(cdate.getNormalizedYear())) {
                    int weekOfYear = internalGet(WEEK_OF_YEAR);
                    if (weekOfYear > 1 && weekOfYear < 52) {
                        set(WEEK_OF_YEAR, weekOfYear);
                        max = SATURDAY;
                        break;
                    }
                }
                amount %= 7;
                if (amount == 0) {
                    return;
                }
                long fd = getCurrentFixedDate();
                long dowFirst = calsys.getDayOfWeekDateOnOrBefore(fd, getFirstDayOfWeek());
                fd += amount;
                if (fd < dowFirst) {
                    fd += 7;
                } else if (fd >= dowFirst + 7) {
                    fd -= 7;
                }
                BaseCalendar$Date d = getCalendarDate(fd);
                set(ERA, (d.getNormalizedYear() <= 0 ? BCE : CE));
                set(d.getYear(), d.getMonth() - 1, d.getDayOfMonth());
                return;
            }
        
        case DAY_OF_WEEK_IN_MONTH: 
            {
                min = 1;
                if (!isCutoverYear(cdate.getNormalizedYear())) {
                    int dom = internalGet(DAY_OF_MONTH);
                    int monthLength = calsys.getMonthLength(cdate);
                    int lastDays = monthLength % 7;
                    max = monthLength / 7;
                    int x = (dom - 1) % 7;
                    if (x < lastDays) {
                        max++;
                    }
                    set(DAY_OF_WEEK, internalGet(DAY_OF_WEEK));
                    break;
                }
                long fd = getCurrentFixedDate();
                long month1 = getFixedDateMonth1(cdate, fd);
                int monthLength = actualMonthLength();
                int lastDays = monthLength % 7;
                max = monthLength / 7;
                int x = (int)(fd - month1) % 7;
                if (x < lastDays) {
                    max++;
                }
                int value = getRolledValue(internalGet(field), amount, min, max) - 1;
                fd = month1 + value * 7 + x;
                BaseCalendar cal = (fd >= gregorianCutoverDate) ? gcal : getJulianCalendarSystem();
                BaseCalendar$Date d = (BaseCalendar$Date)(BaseCalendar$Date)cal.newCalendarDate(TimeZone.NO_TIMEZONE);
                cal.getCalendarDateFromFixedDate(d, fd);
                set(DAY_OF_MONTH, d.getDayOfMonth());
                return;
            }
        
        }
        set(field, getRolledValue(internalGet(field), amount, min, max));
    }
    
    public int getMinimum(int field) {
        return MIN_VALUES[field];
    }
    
    public int getMaximum(int field) {
        switch (field) {
        case MONTH: 
        
        case DAY_OF_MONTH: 
        
        case DAY_OF_YEAR: 
        
        case WEEK_OF_YEAR: 
        
        case WEEK_OF_MONTH: 
        
        case DAY_OF_WEEK_IN_MONTH: 
        
        case YEAR: 
            {
                if (gregorianCutoverYear > 200) {
                    break;
                }
                GregorianCalendar gc = (GregorianCalendar)(GregorianCalendar)clone();
                gc.setLenient(true);
                gc.setTimeInMillis(gregorianCutover);
                int v1 = gc.getActualMaximum(field);
                gc.setTimeInMillis(gregorianCutover - 1);
                int v2 = gc.getActualMaximum(field);
                return Math.max(MAX_VALUES[field], Math.max(v1, v2));
            }
        
        }
        return MAX_VALUES[field];
    }
    
    public int getGreatestMinimum(int field) {
        if (field == DAY_OF_MONTH) {
            BaseCalendar$Date d = getGregorianCutoverDate();
            long mon1 = getFixedDateMonth1(d, gregorianCutoverDate);
            d = getCalendarDate(mon1);
            return Math.max(MIN_VALUES[field], d.getDayOfMonth());
        }
        return MIN_VALUES[field];
    }
    
    public int getLeastMaximum(int field) {
        switch (field) {
        case MONTH: 
        
        case DAY_OF_MONTH: 
        
        case DAY_OF_YEAR: 
        
        case WEEK_OF_YEAR: 
        
        case WEEK_OF_MONTH: 
        
        case DAY_OF_WEEK_IN_MONTH: 
        
        case YEAR: 
            {
                GregorianCalendar gc = (GregorianCalendar)(GregorianCalendar)clone();
                gc.setLenient(true);
                gc.setTimeInMillis(gregorianCutover);
                int v1 = gc.getActualMaximum(field);
                gc.setTimeInMillis(gregorianCutover - 1);
                int v2 = gc.getActualMaximum(field);
                return Math.min(LEAST_MAX_VALUES[field], Math.min(v1, v2));
            }
        
        }
        return LEAST_MAX_VALUES[field];
    }
    
    public int getActualMinimum(int field) {
        if (field == DAY_OF_MONTH) {
            GregorianCalendar gc = getNormalizedCalendar();
            int year = gc.cdate.getNormalizedYear();
            if (year == gregorianCutoverYear || year == gregorianCutoverYearJulian) {
                long month1 = getFixedDateMonth1(gc.cdate, gc.calsys.getFixedDate(gc.cdate));
                BaseCalendar$Date d = getCalendarDate(month1);
                return d.getDayOfMonth();
            }
        }
        return getMinimum(field);
    }
    
    public int getActualMaximum(int field) {
        final int fieldsForFixedMax = ERA_MASK | DAY_OF_WEEK_MASK | HOUR_MASK | AM_PM_MASK | HOUR_OF_DAY_MASK | MINUTE_MASK | SECOND_MASK | MILLISECOND_MASK | ZONE_OFFSET_MASK | DST_OFFSET_MASK;
        if ((fieldsForFixedMax & (1 << field)) != 0) {
            return getMaximum(field);
        }
        GregorianCalendar gc = getNormalizedCalendar();
        BaseCalendar$Date date = gc.cdate;
        BaseCalendar cal = gc.calsys;
        int normalizedYear = date.getNormalizedYear();
        int value = -1;
        switch (field) {
        case MONTH: 
            {
                if (!gc.isCutoverYear(normalizedYear)) {
                    value = DECEMBER;
                    break;
                }
                long nextJan1;
                do {
                    nextJan1 = gcal.getFixedDate(++normalizedYear, BaseCalendar.JANUARY, 1, null);
                }                 while (nextJan1 < gregorianCutoverDate);
                BaseCalendar$Date d = (BaseCalendar$Date)(BaseCalendar$Date)date.clone();
                cal.getCalendarDateFromFixedDate(d, nextJan1 - 1);
                value = d.getMonth() - 1;
            }
            break;
        
        case DAY_OF_MONTH: 
            {
                value = cal.getMonthLength(date);
                if (!gc.isCutoverYear(normalizedYear) || date.getDayOfMonth() == value) {
                    break;
                }
                long fd = gc.getCurrentFixedDate();
                if (fd >= gregorianCutoverDate) {
                    break;
                }
                int monthLength = gc.actualMonthLength();
                long monthEnd = gc.getFixedDateMonth1(gc.cdate, fd) + monthLength - 1;
                BaseCalendar$Date d = gc.getCalendarDate(monthEnd);
                value = d.getDayOfMonth();
            }
            break;
        
        case DAY_OF_YEAR: 
            {
                if (!gc.isCutoverYear(normalizedYear)) {
                    value = cal.getYearLength(date);
                    break;
                }
                long jan1;
                if (gregorianCutoverYear == gregorianCutoverYearJulian) {
                    BaseCalendar cocal = gc.getCutoverCalendarSystem();
                    jan1 = cocal.getFixedDate(normalizedYear, 1, 1, null);
                } else if (normalizedYear == gregorianCutoverYearJulian) {
                    jan1 = cal.getFixedDate(normalizedYear, 1, 1, null);
                } else {
                    jan1 = gregorianCutoverDate;
                }
                long nextJan1 = gcal.getFixedDate(++normalizedYear, 1, 1, null);
                if (nextJan1 < gregorianCutoverDate) {
                    nextJan1 = gregorianCutoverDate;
                }
                if (!$assertionsDisabled && !(jan1 <= cal.getFixedDate(date.getNormalizedYear(), date.getMonth(), date.getDayOfMonth(), date))) throw new AssertionError();
                if (!$assertionsDisabled && !(nextJan1 >= cal.getFixedDate(date.getNormalizedYear(), date.getMonth(), date.getDayOfMonth(), date))) throw new AssertionError();
                value = (int)(nextJan1 - jan1);
            }
            break;
        
        case WEEK_OF_YEAR: 
            {
                if (!gc.isCutoverYear(normalizedYear)) {
                    CalendarDate d = cal.newCalendarDate(TimeZone.NO_TIMEZONE);
                    d.setDate(date.getYear(), BaseCalendar.JANUARY, 1);
                    int dayOfWeek = cal.getDayOfWeek(d);
                    dayOfWeek -= getFirstDayOfWeek();
                    if (dayOfWeek < 0) {
                        dayOfWeek += 7;
                    }
                    value = 52;
                    int magic = dayOfWeek + getMinimalDaysInFirstWeek() - 1;
                    if ((magic == 6) || (date.isLeapYear() && (magic == 5 || magic == 12))) {
                        value++;
                    }
                    break;
                }
                if (gc == this) {
                    gc = (GregorianCalendar)(GregorianCalendar)gc.clone();
                }
                gc.set(DAY_OF_YEAR, getActualMaximum(DAY_OF_YEAR));
                value = gc.get(WEEK_OF_YEAR);
            }
            break;
        
        case WEEK_OF_MONTH: 
            {
                if (!gc.isCutoverYear(normalizedYear)) {
                    CalendarDate d = cal.newCalendarDate(null);
                    d.setDate(date.getYear(), date.getMonth(), 1);
                    int dayOfWeek = cal.getDayOfWeek(d);
                    int monthLength = cal.getMonthLength(d);
                    dayOfWeek -= getFirstDayOfWeek();
                    if (dayOfWeek < 0) {
                        dayOfWeek += 7;
                    }
                    int nDaysFirstWeek = 7 - dayOfWeek;
                    value = 3;
                    if (nDaysFirstWeek >= getMinimalDaysInFirstWeek()) {
                        value++;
                    }
                    monthLength -= nDaysFirstWeek + 7 * 3;
                    if (monthLength > 0) {
                        value++;
                        if (monthLength > 7) {
                            value++;
                        }
                    }
                    break;
                }
                if (gc == this) {
                    gc = (GregorianCalendar)(GregorianCalendar)gc.clone();
                }
                int y = gc.internalGet(YEAR);
                int m = gc.internalGet(MONTH);
                do {
                    value = gc.get(WEEK_OF_MONTH);
                    gc.add(WEEK_OF_MONTH, +1);
                }                 while (gc.get(YEAR) == y && gc.get(MONTH) == m);
            }
            break;
        
        case DAY_OF_WEEK_IN_MONTH: 
            {
                int ndays;
                int dow1;
                int dow = date.getDayOfWeek();
                if (!gc.isCutoverYear(normalizedYear)) {
                    BaseCalendar$Date d = (BaseCalendar$Date)(BaseCalendar$Date)date.clone();
                    ndays = cal.getMonthLength(d);
                    d.setDayOfMonth(1);
                    cal.normalize(d);
                    dow1 = d.getDayOfWeek();
                } else {
                    if (gc == this) {
                        gc = (GregorianCalendar)(GregorianCalendar)clone();
                    }
                    ndays = gc.actualMonthLength();
                    gc.set(DAY_OF_MONTH, gc.getActualMinimum(DAY_OF_MONTH));
                    dow1 = gc.get(DAY_OF_WEEK);
                }
                int x = dow - dow1;
                if (x < 0) {
                    x += 7;
                }
                ndays -= x;
                value = (ndays + 6) / 7;
            }
            break;
        
        case YEAR: 
            {
                if (gc == this) {
                    gc = (GregorianCalendar)(GregorianCalendar)clone();
                }
                long current = gc.getYearOffsetInMillis();
                if (gc.internalGetEra() == CE) {
                    gc.setTimeInMillis(Long.MAX_VALUE);
                    value = gc.get(YEAR);
                    long maxEnd = gc.getYearOffsetInMillis();
                    if (current > maxEnd) {
                        value--;
                    }
                } else {
                    CalendarSystem mincal = gc.getTimeInMillis() >= gregorianCutover ? gcal : getJulianCalendarSystem();
                    CalendarDate d = mincal.getCalendarDate(Long.MIN_VALUE, getZone());
                    long maxEnd = (cal.getDayOfYear(d) - 1) * 24 + d.getHours();
                    maxEnd *= 60;
                    maxEnd += d.getMinutes();
                    maxEnd *= 60;
                    maxEnd += d.getSeconds();
                    maxEnd *= 1000;
                    maxEnd += d.getMillis();
                    value = d.getYear();
                    if (value <= 0) {
                        if (!$assertionsDisabled && !(mincal == gcal)) throw new AssertionError();
                        value = 1 - value;
                    }
                    if (current < maxEnd) {
                        value--;
                    }
                }
            }
            break;
        
        default: 
            throw new ArrayIndexOutOfBoundsException(field);
        
        }
        return value;
    }
    
    private final long getYearOffsetInMillis() {
        long t = (internalGet(DAY_OF_YEAR) - 1) * 24;
        t += internalGet(HOUR_OF_DAY);
        t *= 60;
        t += internalGet(MINUTE);
        t *= 60;
        t += internalGet(SECOND);
        t *= 1000;
        return t + internalGet(MILLISECOND) - (internalGet(ZONE_OFFSET) + internalGet(DST_OFFSET));
    }
    
    public Object clone() {
        GregorianCalendar other = (GregorianCalendar)(GregorianCalendar)super.clone();
        other.gdate = (BaseCalendar$Date)(BaseCalendar$Date)gdate.clone();
        if (cdate != null) {
            if (cdate != gdate) {
                other.cdate = (BaseCalendar$Date)(BaseCalendar$Date)cdate.clone();
            } else {
                other.cdate = other.gdate;
            }
        }
        other.originalFields = null;
        other.zoneOffsets = null;
        return other;
    }
    
    public TimeZone getTimeZone() {
        TimeZone zone = super.getTimeZone();
        gdate.setZone(zone);
        if (cdate != null && cdate != gdate) {
            cdate.setZone(zone);
        }
        return zone;
    }
    
    public void setTimeZone(TimeZone zone) {
        super.setTimeZone(zone);
        gdate.setZone(zone);
        if (cdate != null && cdate != gdate) {
            cdate.setZone(zone);
        }
    }
    private transient long cachedFixedDate = Long.MIN_VALUE;
    
    protected void computeFields() {
        int mask = 0;
        if (isPartiallyNormalized()) {
            mask = getSetStateFields();
            int fieldMask = ~mask & ALL_FIELDS;
            if (fieldMask != 0 || calsys == null) {
                mask |= computeFields(fieldMask, mask & (ZONE_OFFSET_MASK | DST_OFFSET_MASK));
                if (!$assertionsDisabled && !(mask == ALL_FIELDS)) throw new AssertionError();
            }
        } else {
            mask = ALL_FIELDS;
            computeFields(mask, 0);
        }
        setFieldsComputed(mask);
    }
    
    private int computeFields(int fieldMask, int tzMask) {
        int zoneOffset = 0;
        TimeZone tz = getZone();
        if (zoneOffsets == null) {
            zoneOffsets = new int[2];
        }
        if (tzMask != (ZONE_OFFSET_MASK | DST_OFFSET_MASK)) {
            if (tz instanceof ZoneInfo) {
                zoneOffset = ((ZoneInfo)(ZoneInfo)tz).getOffsets(time, zoneOffsets);
            } else {
                zoneOffset = tz.getOffset(time);
                zoneOffsets[0] = tz.getRawOffset();
                zoneOffsets[1] = zoneOffset - zoneOffsets[0];
            }
        }
        if (tzMask != 0) {
            if (isFieldSet(tzMask, ZONE_OFFSET)) {
                zoneOffsets[0] = internalGet(ZONE_OFFSET);
            }
            if (isFieldSet(tzMask, DST_OFFSET)) {
                zoneOffsets[1] = internalGet(DST_OFFSET);
            }
            zoneOffset = zoneOffsets[0] + zoneOffsets[1];
        }
        long fixedDate = zoneOffset / ONE_DAY;
        int timeOfDay = zoneOffset % (int)ONE_DAY;
        fixedDate += time / ONE_DAY;
        timeOfDay += (int)(time % ONE_DAY);
        if (timeOfDay >= ONE_DAY) {
            timeOfDay -= ONE_DAY;
            ++fixedDate;
        } else {
            while (timeOfDay < 0) {
                timeOfDay += ONE_DAY;
                --fixedDate;
            }
        }
        fixedDate += EPOCH_OFFSET;
        int era = CE;
        int year;
        if (fixedDate >= gregorianCutoverDate) {
            if (!$assertionsDisabled && !(cachedFixedDate == Long.MIN_VALUE || gdate.isNormalized())) throw new AssertionError("cache control: not normalized");
            if (!$assertionsDisabled && !(cachedFixedDate == Long.MIN_VALUE || gcal.getFixedDate(gdate.getNormalizedYear(), gdate.getMonth(), gdate.getDayOfMonth(), gdate) == cachedFixedDate)) throw new AssertionError("cache control: inconsictency" + ", cachedFixedDate=" + cachedFixedDate + ", computed=" + gcal.getFixedDate(gdate.getNormalizedYear(), gdate.getMonth(), gdate.getDayOfMonth(), gdate) + ", date=" + gdate);
            if (fixedDate != cachedFixedDate) {
                gcal.getCalendarDateFromFixedDate(gdate, fixedDate);
                cachedFixedDate = fixedDate;
            }
            year = gdate.getYear();
            if (year <= 0) {
                year = 1 - year;
                era = BCE;
            }
            calsys = gcal;
            cdate = gdate;
            if (!$assertionsDisabled && !(cdate.getDayOfWeek() > 0)) throw new AssertionError("dow=" + cdate.getDayOfWeek() + ", date=" + cdate);
        } else {
            calsys = getJulianCalendarSystem();
            cdate = (BaseCalendar$Date)(BaseCalendar$Date)jcal.newCalendarDate(getZone());
            jcal.getCalendarDateFromFixedDate(cdate, fixedDate);
            Era e = cdate.getEra();
            if (e == jeras[0]) {
                era = BCE;
            }
            year = cdate.getYear();
        }
        internalSet(ERA, era);
        internalSet(YEAR, year);
        int mask = fieldMask | (ERA_MASK | YEAR_MASK);
        int month = cdate.getMonth() - 1;
        int dayOfMonth = cdate.getDayOfMonth();
        if ((fieldMask & (MONTH_MASK | DAY_OF_MONTH_MASK | DAY_OF_WEEK_MASK)) != 0) {
            internalSet(MONTH, month);
            internalSet(DAY_OF_MONTH, dayOfMonth);
            internalSet(DAY_OF_WEEK, cdate.getDayOfWeek());
            mask |= MONTH_MASK | DAY_OF_MONTH_MASK | DAY_OF_WEEK_MASK;
        }
        if ((fieldMask & (HOUR_OF_DAY_MASK | AM_PM_MASK | HOUR_MASK | MINUTE_MASK | SECOND_MASK | MILLISECOND_MASK)) != 0) {
            if (timeOfDay != 0) {
                int hours = timeOfDay / ONE_HOUR;
                internalSet(HOUR_OF_DAY, hours);
                internalSet(AM_PM, hours / 12);
                internalSet(HOUR, hours % 12);
                int r = timeOfDay % ONE_HOUR;
                internalSet(MINUTE, r / ONE_MINUTE);
                r %= ONE_MINUTE;
                internalSet(SECOND, r / ONE_SECOND);
                internalSet(MILLISECOND, r % ONE_SECOND);
            } else {
                internalSet(HOUR_OF_DAY, 0);
                internalSet(AM_PM, AM);
                internalSet(HOUR, 0);
                internalSet(MINUTE, 0);
                internalSet(SECOND, 0);
                internalSet(MILLISECOND, 0);
            }
            mask |= (HOUR_OF_DAY_MASK | AM_PM_MASK | HOUR_MASK | MINUTE_MASK | SECOND_MASK | MILLISECOND_MASK);
        }
        if ((fieldMask & (ZONE_OFFSET_MASK | DST_OFFSET_MASK)) != 0) {
            internalSet(ZONE_OFFSET, zoneOffsets[0]);
            internalSet(DST_OFFSET, zoneOffsets[1]);
            mask |= (ZONE_OFFSET_MASK | DST_OFFSET_MASK);
        }
        if ((fieldMask & (DAY_OF_YEAR_MASK | WEEK_OF_YEAR_MASK | WEEK_OF_MONTH_MASK | DAY_OF_WEEK_IN_MONTH_MASK)) != 0) {
            int normalizedYear = cdate.getNormalizedYear();
            long fixedDateJan1 = calsys.getFixedDate(normalizedYear, 1, 1, cdate);
            int dayOfYear = (int)(fixedDate - fixedDateJan1) + 1;
            long fixedDateMonth1 = fixedDate - dayOfMonth + 1;
            int cutoverGap = 0;
            int cutoverYear = (calsys == gcal) ? gregorianCutoverYear : gregorianCutoverYearJulian;
            int relativeDayOfMonth = dayOfMonth - 1;
            if (normalizedYear == cutoverYear) {
                if (getCutoverCalendarSystem() == jcal) {
                    fixedDateJan1 = getFixedDateJan1(cdate, fixedDate);
                    if (fixedDate >= gregorianCutoverDate) {
                        fixedDateMonth1 = getFixedDateMonth1(cdate, fixedDate);
                    }
                }
                int realDayOfYear = (int)(fixedDate - fixedDateJan1) + 1;
                cutoverGap = dayOfYear - realDayOfYear;
                dayOfYear = realDayOfYear;
                relativeDayOfMonth = (int)(fixedDate - fixedDateMonth1);
            }
            internalSet(DAY_OF_YEAR, dayOfYear);
            internalSet(DAY_OF_WEEK_IN_MONTH, relativeDayOfMonth / 7 + 1);
            int weekOfYear = getWeekNumber(fixedDateJan1, fixedDate);
            if (weekOfYear == 0) {
                long fixedDec31 = fixedDateJan1 - 1;
                long prevJan1;
                if (normalizedYear > (cutoverYear + 1)) {
                    prevJan1 = fixedDateJan1 - 365;
                    if (CalendarUtils.isGregorianLeapYear(normalizedYear - 1)) {
                        --prevJan1;
                    }
                } else {
                    BaseCalendar calForJan1 = calsys;
                    int prevYear = normalizedYear - 1;
                    if (prevYear == cutoverYear) {
                        calForJan1 = getCutoverCalendarSystem();
                    }
                    prevJan1 = calForJan1.getFixedDate(prevYear, BaseCalendar.JANUARY, 1, null);
                    while (prevJan1 > fixedDec31) {
                        prevJan1 = getJulianCalendarSystem().getFixedDate(--prevYear, BaseCalendar.JANUARY, 1, null);
                    }
                }
                weekOfYear = getWeekNumber(prevJan1, fixedDec31);
            } else {
                if (normalizedYear > gregorianCutoverYear || normalizedYear < (gregorianCutoverYearJulian - 1)) {
                    if (weekOfYear >= 52) {
                        long nextJan1 = fixedDateJan1 + 365;
                        if (cdate.isLeapYear()) {
                            nextJan1++;
                        }
                        long nextJan1st = calsys.getDayOfWeekDateOnOrBefore(nextJan1 + 6, getFirstDayOfWeek());
                        int ndays = (int)(nextJan1st - nextJan1);
                        if (ndays >= getMinimalDaysInFirstWeek() && fixedDate >= (nextJan1st - 7)) {
                            weekOfYear = 1;
                        }
                    }
                } else {
                    BaseCalendar calForJan1 = calsys;
                    int nextYear = normalizedYear + 1;
                    if (nextYear == (gregorianCutoverYearJulian + 1) && nextYear < gregorianCutoverYear) {
                        nextYear = gregorianCutoverYear;
                    }
                    if (nextYear == gregorianCutoverYear) {
                        calForJan1 = getCutoverCalendarSystem();
                    }
                    long nextJan1 = calForJan1.getFixedDate(nextYear, BaseCalendar.JANUARY, 1, null);
                    if (nextJan1 < fixedDate) {
                        nextJan1 = gregorianCutoverDate;
                        calForJan1 = gcal;
                    }
                    long nextJan1st = calForJan1.getDayOfWeekDateOnOrBefore(nextJan1 + 6, getFirstDayOfWeek());
                    int ndays = (int)(nextJan1st - nextJan1);
                    if (ndays >= getMinimalDaysInFirstWeek() && fixedDate >= (nextJan1st - 7)) {
                        weekOfYear = 1;
                    }
                }
            }
            internalSet(WEEK_OF_YEAR, weekOfYear);
            internalSet(WEEK_OF_MONTH, getWeekNumber(fixedDateMonth1, fixedDate));
            mask |= (DAY_OF_YEAR_MASK | WEEK_OF_YEAR_MASK | WEEK_OF_MONTH_MASK | DAY_OF_WEEK_IN_MONTH_MASK);
        }
        return mask;
    }
    
    private final int getWeekNumber(long fixedDay1, long fixedDate) {
        long fixedDay1st = gcal.getDayOfWeekDateOnOrBefore(fixedDay1 + 6, getFirstDayOfWeek());
        int ndays = (int)(fixedDay1st - fixedDay1);
        if (!$assertionsDisabled && !(ndays <= 7)) throw new AssertionError();
        if (ndays >= getMinimalDaysInFirstWeek()) {
            fixedDay1st -= 7;
        }
        int normalizedDayOfPeriod = (int)(fixedDate - fixedDay1st);
        if (normalizedDayOfPeriod >= 0) {
            return normalizedDayOfPeriod / 7 + 1;
        }
        return CalendarUtils.floorDivide(normalizedDayOfPeriod, 7) + 1;
    }
    
    protected void computeTime() {
        if (!isLenient()) {
            if (originalFields == null) {
                originalFields = new int[FIELD_COUNT];
            }
            for (int field = 0; field < FIELD_COUNT; field++) {
                int value = internalGet(field);
                if (isExternallySet(field)) {
                    if (value < getMinimum(field) || value > getMaximum(field)) {
                        throw new IllegalArgumentException(getFieldName(field));
                    }
                }
                originalFields[field] = value;
            }
        }
        int fieldMask = selectFields();
        int year = isSet(YEAR) ? internalGet(YEAR) : EPOCH_YEAR;
        int era = internalGetEra();
        if (era == BCE) {
            year = 1 - year;
        } else if (era != CE) {
            throw new IllegalArgumentException("Invalid era");
        }
        if (year <= 0 && !isSet(ERA)) {
            fieldMask |= ERA_MASK;
            setFieldsComputed(ERA_MASK);
        }
        long timeOfDay = 0;
        if (isFieldSet(fieldMask, HOUR_OF_DAY)) {
            timeOfDay += (long)internalGet(HOUR_OF_DAY);
        } else {
            timeOfDay += internalGet(HOUR);
            if (isFieldSet(fieldMask, AM_PM)) {
                timeOfDay += 12 * internalGet(AM_PM);
            }
        }
        timeOfDay *= 60;
        timeOfDay += internalGet(MINUTE);
        timeOfDay *= 60;
        timeOfDay += internalGet(SECOND);
        timeOfDay *= 1000;
        timeOfDay += internalGet(MILLISECOND);
        long fixedDate = timeOfDay / ONE_DAY;
        timeOfDay %= ONE_DAY;
        while (timeOfDay < 0) {
            timeOfDay += ONE_DAY;
            --fixedDate;
        }
        calculateFixedDate: {
            long gfd;
            long jfd;
            if (year > gregorianCutoverYear && year > gregorianCutoverYearJulian) {
                gfd = fixedDate + getFixedDate(gcal, year, fieldMask);
                if (gfd >= gregorianCutoverDate) {
                    fixedDate = gfd;
                    break calculateFixedDate;
                }
                jfd = fixedDate + getFixedDate(getJulianCalendarSystem(), year, fieldMask);
            } else if (year < gregorianCutoverYear && year < gregorianCutoverYearJulian) {
                jfd = fixedDate + getFixedDate(getJulianCalendarSystem(), year, fieldMask);
                if (jfd < gregorianCutoverDate) {
                    fixedDate = jfd;
                    break calculateFixedDate;
                }
                gfd = fixedDate + getFixedDate(gcal, year, fieldMask);
            } else {
                gfd = fixedDate + getFixedDate(gcal, year, fieldMask);
                jfd = fixedDate + getFixedDate(getJulianCalendarSystem(), year, fieldMask);
            }
            if (gfd >= gregorianCutoverDate) {
                if (jfd >= gregorianCutoverDate) {
                    fixedDate = gfd;
                } else {
                    if (calsys == gcal || calsys == null) {
                        fixedDate = gfd;
                    } else {
                        fixedDate = jfd;
                    }
                }
            } else {
                if (jfd < gregorianCutoverDate) {
                    fixedDate = jfd;
                } else {
                    if (!isLenient()) {
                        throw new IllegalArgumentException("the specified date doesn\'t exist");
                    }
                    fixedDate = jfd;
                }
            }
        }
        long millis = (fixedDate - EPOCH_OFFSET) * ONE_DAY + timeOfDay;
        TimeZone zone = getZone();
        if (zoneOffsets == null) {
            zoneOffsets = new int[2];
        }
        int tzMask = fieldMask & (ZONE_OFFSET_MASK | DST_OFFSET_MASK);
        if (tzMask != (ZONE_OFFSET_MASK | DST_OFFSET_MASK)) {
            if (zone instanceof ZoneInfo) {
                ((ZoneInfo)(ZoneInfo)zone).getOffsetsByWall(millis, zoneOffsets);
            } else {
                int gmtOffset = isFieldSet(fieldMask, ZONE_OFFSET) ? internalGet(ZONE_OFFSET) : zone.getRawOffset();
                zone.getOffsets(millis - gmtOffset, zoneOffsets);
            }
        }
        if (tzMask != 0) {
            if (isFieldSet(tzMask, ZONE_OFFSET)) {
                zoneOffsets[0] = internalGet(ZONE_OFFSET);
            }
            if (isFieldSet(tzMask, DST_OFFSET)) {
                zoneOffsets[1] = internalGet(DST_OFFSET);
            }
        }
        millis -= zoneOffsets[0] + zoneOffsets[1];
        time = millis;
        int mask = computeFields(fieldMask | getSetStateFields(), tzMask);
        if (!isLenient()) {
            for (int field = 0; field < FIELD_COUNT; field++) {
                if (!isExternallySet(field)) {
                    continue;
                }
                if (originalFields[field] != internalGet(field)) {
                    System.arraycopy(originalFields, 0, fields, 0, fields.length);
                    throw new IllegalArgumentException(getFieldName(field));
                }
            }
        }
        setFieldsNormalized(mask);
    }
    
    private long getFixedDate(BaseCalendar cal, int year, int fieldMask) {
        int month = JANUARY;
        if (isFieldSet(fieldMask, MONTH)) {
            month = internalGet(MONTH);
            if (month > DECEMBER) {
                year += month / 12;
                month %= 12;
            } else if (month < JANUARY) {
                int[] rem = new int[1];
                year += CalendarUtils.floorDivide(month, 12, rem);
                month = rem[0];
            }
        }
        long fixedDate = cal.getFixedDate(year, month + 1, 1, cal == gcal ? gdate : null);
        if (isFieldSet(fieldMask, MONTH)) {
            if (isFieldSet(fieldMask, DAY_OF_MONTH)) {
                if (isSet(DAY_OF_MONTH)) {
                    fixedDate += internalGet(DAY_OF_MONTH);
                    fixedDate--;
                }
            } else {
                if (isFieldSet(fieldMask, WEEK_OF_MONTH)) {
                    long firstDayOfWeek = cal.getDayOfWeekDateOnOrBefore(fixedDate + 6, getFirstDayOfWeek());
                    if ((firstDayOfWeek - fixedDate) >= getMinimalDaysInFirstWeek()) {
                        firstDayOfWeek -= 7;
                    }
                    if (isFieldSet(fieldMask, DAY_OF_WEEK)) {
                        firstDayOfWeek = cal.getDayOfWeekDateOnOrBefore(firstDayOfWeek + 6, internalGet(DAY_OF_WEEK));
                    }
                    fixedDate = firstDayOfWeek + 7 * (internalGet(WEEK_OF_MONTH) - 1);
                } else {
                    int dayOfWeek;
                    if (isFieldSet(fieldMask, DAY_OF_WEEK)) {
                        dayOfWeek = internalGet(DAY_OF_WEEK);
                    } else {
                        dayOfWeek = getFirstDayOfWeek();
                    }
                    int dowim;
                    if (isFieldSet(fieldMask, DAY_OF_WEEK_IN_MONTH)) {
                        dowim = internalGet(DAY_OF_WEEK_IN_MONTH);
                    } else {
                        dowim = 1;
                    }
                    if (dowim >= 0) {
                        fixedDate = cal.getDayOfWeekDateOnOrBefore(fixedDate + (7 * dowim) - 1, dayOfWeek);
                    } else {
                        int lastDate = monthLength(month, year) + (7 * (dowim + 1));
                        fixedDate = cal.getDayOfWeekDateOnOrBefore(fixedDate + lastDate - 1, dayOfWeek);
                    }
                }
            }
        } else {
            if (year == gregorianCutoverYear && cal == gcal && fixedDate < gregorianCutoverDate && gregorianCutoverYear != gregorianCutoverYearJulian) {
                fixedDate = gregorianCutoverDate;
            }
            if (isFieldSet(fieldMask, DAY_OF_YEAR)) {
                fixedDate += internalGet(DAY_OF_YEAR);
                fixedDate--;
            } else {
                long firstDayOfWeek = cal.getDayOfWeekDateOnOrBefore(fixedDate + 6, getFirstDayOfWeek());
                if ((firstDayOfWeek - fixedDate) >= getMinimalDaysInFirstWeek()) {
                    firstDayOfWeek -= 7;
                }
                if (isFieldSet(fieldMask, DAY_OF_WEEK)) {
                    int dayOfWeek = internalGet(DAY_OF_WEEK);
                    if (dayOfWeek != getFirstDayOfWeek()) {
                        firstDayOfWeek = cal.getDayOfWeekDateOnOrBefore(firstDayOfWeek + 6, dayOfWeek);
                    }
                }
                fixedDate = firstDayOfWeek + 7 * ((long)internalGet(WEEK_OF_YEAR) - 1);
            }
        }
        return fixedDate;
    }
    
    private final GregorianCalendar getNormalizedCalendar() {
        GregorianCalendar gc;
        if (isFullyNormalized()) {
            gc = this;
        } else {
            gc = (GregorianCalendar)(GregorianCalendar)this.clone();
            gc.setLenient(true);
            gc.complete();
        }
        return gc;
    }
    
    private static final synchronized BaseCalendar getJulianCalendarSystem() {
        if (jcal == null) {
            jcal = (JulianCalendar)(JulianCalendar)CalendarSystem.forName("julian");
            jeras = jcal.getEras();
        }
        return jcal;
    }
    
    private BaseCalendar getCutoverCalendarSystem() {
        CalendarDate date = getGregorianCutoverDate();
        if (date.getMonth() == BaseCalendar.JANUARY && date.getDayOfMonth() == 1) {
            return gcal;
        }
        return getJulianCalendarSystem();
    }
    
    private final boolean isCutoverYear(int normalizedYear) {
        int cutoverYear = (calsys == gcal) ? gregorianCutoverYear : gregorianCutoverYearJulian;
        return normalizedYear == cutoverYear;
    }
    
    private final long getFixedDateJan1(BaseCalendar$Date date, long fixedDate) {
        if (!$assertionsDisabled && !(date.getNormalizedYear() == gregorianCutoverYear || date.getNormalizedYear() == gregorianCutoverYearJulian)) throw new AssertionError();
        if (gregorianCutoverYear != gregorianCutoverYearJulian) {
            if (fixedDate >= gregorianCutoverDate) {
                return gregorianCutoverDate;
            }
        }
        BaseCalendar jcal = getJulianCalendarSystem();
        return jcal.getFixedDate(date.getNormalizedYear(), BaseCalendar.JANUARY, 1, null);
    }
    
    private final long getFixedDateMonth1(BaseCalendar$Date date, long fixedDate) {
        if (!$assertionsDisabled && !(date.getNormalizedYear() == gregorianCutoverYear || date.getNormalizedYear() == gregorianCutoverYearJulian)) throw new AssertionError();
        BaseCalendar$Date gCutover = getGregorianCutoverDate();
        if (gCutover.getMonth() == BaseCalendar.JANUARY && gCutover.getDayOfMonth() == 1) {
            return fixedDate - date.getDayOfMonth() + 1;
        }
        long fixedDateMonth1;
        if (date.getMonth() == gCutover.getMonth()) {
            BaseCalendar$Date jLastDate = getLastJulianDate();
            if (gregorianCutoverYear == gregorianCutoverYearJulian && gCutover.getMonth() == jLastDate.getMonth()) {
                fixedDateMonth1 = jcal.getFixedDate(date.getNormalizedYear(), date.getMonth(), 1, null);
            } else {
                fixedDateMonth1 = gregorianCutoverDate;
            }
        } else {
            fixedDateMonth1 = fixedDate - date.getDayOfMonth() + 1;
        }
        return fixedDateMonth1;
    }
    
    private final BaseCalendar$Date getCalendarDate(long fd) {
        BaseCalendar cal = (fd >= gregorianCutoverDate) ? gcal : getJulianCalendarSystem();
        BaseCalendar$Date d = (BaseCalendar$Date)(BaseCalendar$Date)cal.newCalendarDate(TimeZone.NO_TIMEZONE);
        cal.getCalendarDateFromFixedDate(d, fd);
        return d;
    }
    
    private final BaseCalendar$Date getGregorianCutoverDate() {
        return getCalendarDate(gregorianCutoverDate);
    }
    
    private final BaseCalendar$Date getLastJulianDate() {
        return getCalendarDate(gregorianCutoverDate - 1);
    }
    
    private final int monthLength(int month, int year) {
        return isLeapYear(year) ? LEAP_MONTH_LENGTH[month] : MONTH_LENGTH[month];
    }
    
    private final int monthLength(int month) {
        int year = internalGet(YEAR);
        if (internalGetEra() == BCE) {
            year = 1 - year;
        }
        return monthLength(month, year);
    }
    
    private final int actualMonthLength() {
        int year = cdate.getNormalizedYear();
        if (year != gregorianCutoverYear && year != gregorianCutoverYearJulian) {
            return calsys.getMonthLength(cdate);
        }
        BaseCalendar$Date date = (BaseCalendar$Date)(BaseCalendar$Date)cdate.clone();
        long fd = calsys.getFixedDate(date);
        long month1 = getFixedDateMonth1(date, fd);
        long next1 = month1 + calsys.getMonthLength(date);
        if (next1 < gregorianCutoverDate) {
            return (int)(next1 - month1);
        }
        if (cdate != gdate) {
            date = (BaseCalendar$Date)(BaseCalendar$Date)gcal.newCalendarDate(TimeZone.NO_TIMEZONE);
        }
        gcal.getCalendarDateFromFixedDate(date, next1);
        next1 = getFixedDateMonth1(date, next1);
        return (int)(next1 - month1);
    }
    
    private final int yearLength(int year) {
        return isLeapYear(year) ? 366 : 365;
    }
    
    private final int yearLength() {
        int year = internalGet(YEAR);
        if (internalGetEra() == BCE) {
            year = 1 - year;
        }
        return yearLength(year);
    }
    
    private final void pinDayOfMonth() {
        int year = internalGet(YEAR);
        int monthLen;
        if (year > gregorianCutoverYear || year < gregorianCutoverYearJulian) {
            monthLen = monthLength(internalGet(MONTH));
        } else {
            GregorianCalendar gc = getNormalizedCalendar();
            monthLen = gc.getActualMaximum(DAY_OF_MONTH);
        }
        int dom = internalGet(DAY_OF_MONTH);
        if (dom > monthLen) {
            set(DAY_OF_MONTH, monthLen);
        }
    }
    
    private final long getCurrentFixedDate() {
        return (calsys == gcal) ? cachedFixedDate : calsys.getFixedDate(cdate);
    }
    
    private static final int getRolledValue(int value, int amount, int min, int max) {
        if (!$assertionsDisabled && !(value >= min && value <= max)) throw new AssertionError();
        int range = max - min + 1;
        amount %= range;
        int n = value + amount;
        if (n > max) {
            n -= range;
        } else if (n < min) {
            n += range;
        }
        if (!$assertionsDisabled && !(n >= min && n <= max)) throw new AssertionError();
        return n;
    }
    
    private final int internalGetEra() {
        return isSet(ERA) ? internalGet(ERA) : CE;
    }
    
    private void readObject(ObjectInputStream stream) throws IOException, ClassNotFoundException {
        stream.defaultReadObject();
        if (gdate == null) {
            gdate = (BaseCalendar$Date)(BaseCalendar$Date)gcal.newCalendarDate(getZone());
            cachedFixedDate = Long.MIN_VALUE;
        }
        setGregorianChange(gregorianCutover);
    }
}
