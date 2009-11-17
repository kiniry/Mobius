package java.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OptionalDataException;
import java.io.Serializable;
import java.security.AccessController;
import java.security.PrivilegedActionException;
import java.text.DateFormat;
import sun.text.resources.LocaleData;
import sun.util.calendar.ZoneInfo;

public abstract class Calendar implements Serializable, Cloneable, Comparable {
    /*synthetic*/ static final boolean $assertionsDisabled = !Calendar.class.desiredAssertionStatus();
    public static final int ERA = 0;
    public static final int YEAR = 1;
    public static final int MONTH = 2;
    public static final int WEEK_OF_YEAR = 3;
    public static final int WEEK_OF_MONTH = 4;
    public static final int DATE = 5;
    public static final int DAY_OF_MONTH = 5;
    public static final int DAY_OF_YEAR = 6;
    public static final int DAY_OF_WEEK = 7;
    public static final int DAY_OF_WEEK_IN_MONTH = 8;
    public static final int AM_PM = 9;
    public static final int HOUR = 10;
    public static final int HOUR_OF_DAY = 11;
    public static final int MINUTE = 12;
    public static final int SECOND = 13;
    public static final int MILLISECOND = 14;
    public static final int ZONE_OFFSET = 15;
    public static final int DST_OFFSET = 16;
    public static final int FIELD_COUNT = 17;
    public static final int SUNDAY = 1;
    public static final int MONDAY = 2;
    public static final int TUESDAY = 3;
    public static final int WEDNESDAY = 4;
    public static final int THURSDAY = 5;
    public static final int FRIDAY = 6;
    public static final int SATURDAY = 7;
    public static final int JANUARY = 0;
    public static final int FEBRUARY = 1;
    public static final int MARCH = 2;
    public static final int APRIL = 3;
    public static final int MAY = 4;
    public static final int JUNE = 5;
    public static final int JULY = 6;
    public static final int AUGUST = 7;
    public static final int SEPTEMBER = 8;
    public static final int OCTOBER = 9;
    public static final int NOVEMBER = 10;
    public static final int DECEMBER = 11;
    public static final int UNDECIMBER = 12;
    public static final int AM = 0;
    public static final int PM = 1;
    protected int[] fields;
    protected boolean[] isSet;
    private transient int[] stamp;
    protected long time;
    protected boolean isTimeSet;
    protected boolean areFieldsSet;
    transient boolean areAllFieldsSet;
    private boolean lenient = true;
    private TimeZone zone;
    private transient boolean sharedZone = false;
    private int firstDayOfWeek;
    private int minimalDaysInFirstWeek;
    private static Hashtable cachedLocaleData = new Hashtable(3);
    private static final int UNSET = 0;
    private static final int COMPUTED = 1;
    private static final int MINIMUM_USER_STAMP = 2;
    static final int ALL_FIELDS = (1 << FIELD_COUNT) - 1;
    private int nextStamp = MINIMUM_USER_STAMP;
    static final int currentSerialVersion = 1;
    private int serialVersionOnStream = currentSerialVersion;
    static final long serialVersionUID = -1807547505821590642L;
    static final int ERA_MASK = (1 << ERA);
    static final int YEAR_MASK = (1 << YEAR);
    static final int MONTH_MASK = (1 << MONTH);
    static final int WEEK_OF_YEAR_MASK = (1 << WEEK_OF_YEAR);
    static final int WEEK_OF_MONTH_MASK = (1 << WEEK_OF_MONTH);
    static final int DAY_OF_MONTH_MASK = (1 << DAY_OF_MONTH);
    static final int DATE_MASK = DAY_OF_MONTH_MASK;
    static final int DAY_OF_YEAR_MASK = (1 << DAY_OF_YEAR);
    static final int DAY_OF_WEEK_MASK = (1 << DAY_OF_WEEK);
    static final int DAY_OF_WEEK_IN_MONTH_MASK = (1 << DAY_OF_WEEK_IN_MONTH);
    static final int AM_PM_MASK = (1 << AM_PM);
    static final int HOUR_MASK = (1 << HOUR);
    static final int HOUR_OF_DAY_MASK = (1 << HOUR_OF_DAY);
    static final int MINUTE_MASK = (1 << MINUTE);
    static final int SECOND_MASK = (1 << SECOND);
    static final int MILLISECOND_MASK = (1 << MILLISECOND);
    static final int ZONE_OFFSET_MASK = (1 << ZONE_OFFSET);
    static final int DST_OFFSET_MASK = (1 << DST_OFFSET);
    
    protected Calendar() {
        this(TimeZone.getDefaultRef(), Locale.getDefault());
        sharedZone = true;
    }
    
    protected Calendar(TimeZone zone, Locale aLocale) {
        
        fields = new int[FIELD_COUNT];
        isSet = new boolean[FIELD_COUNT];
        stamp = new int[FIELD_COUNT];
        this.zone = zone;
        setWeekCountData(aLocale);
    }
    
    public static Calendar getInstance() {
        Calendar cal = createCalendar(TimeZone.getDefaultRef(), Locale.getDefault());
        cal.sharedZone = true;
        return cal;
    }
    
    public static Calendar getInstance(TimeZone zone) {
        return createCalendar(zone, Locale.getDefault());
    }
    
    public static Calendar getInstance(Locale aLocale) {
        Calendar cal = createCalendar(TimeZone.getDefaultRef(), aLocale);
        cal.sharedZone = true;
        return cal;
    }
    
    public static Calendar getInstance(TimeZone zone, Locale aLocale) {
        return createCalendar(zone, aLocale);
    }
    
    private static Calendar createCalendar(TimeZone zone, Locale aLocale) {
        if ("th".equals(aLocale.getLanguage()) && ("TH".equals(aLocale.getCountry()))) {
            return new sun.util.BuddhistCalendar(zone, aLocale);
        }
        return new GregorianCalendar(zone, aLocale);
    }
    
    public static synchronized Locale[] getAvailableLocales() {
        return DateFormat.getAvailableLocales();
    }
    
    protected abstract void computeTime();
    
    protected abstract void computeFields();
    
    public final Date getTime() {
        return new Date(getTimeInMillis());
    }
    
    public final void setTime(Date date) {
        setTimeInMillis(date.getTime());
    }
    
    public long getTimeInMillis() {
        if (!isTimeSet) {
            updateTime();
        }
        return time;
    }
    
    public void setTimeInMillis(long millis) {
        if (time == millis && isTimeSet && areFieldsSet && areAllFieldsSet && (zone instanceof ZoneInfo) && !((ZoneInfo)(ZoneInfo)zone).isDirty()) {
            return;
        }
        time = millis;
        isTimeSet = true;
        areFieldsSet = false;
        computeFields();
        areAllFieldsSet = areFieldsSet = true;
    }
    
    public int get(int field) {
        complete();
        return internalGet(field);
    }
    
    protected final int internalGet(int field) {
        return fields[field];
    }
    
    final void internalSet(int field, int value) {
        fields[field] = value;
    }
    
    public void set(int field, int value) {
        if (isLenient() && areFieldsSet && !areAllFieldsSet) {
            computeFields();
        }
        internalSet(field, value);
        isTimeSet = false;
        areFieldsSet = false;
        isSet[field] = true;
        stamp[field] = nextStamp++;
        if (nextStamp == Integer.MAX_VALUE) {
            adjustStamp();
        }
    }
    
    public final void set(int year, int month, int date) {
        set(YEAR, year);
        set(MONTH, month);
        set(DATE, date);
    }
    
    public final void set(int year, int month, int date, int hourOfDay, int minute) {
        set(YEAR, year);
        set(MONTH, month);
        set(DATE, date);
        set(HOUR_OF_DAY, hourOfDay);
        set(MINUTE, minute);
    }
    
    public final void set(int year, int month, int date, int hourOfDay, int minute, int second) {
        set(YEAR, year);
        set(MONTH, month);
        set(DATE, date);
        set(HOUR_OF_DAY, hourOfDay);
        set(MINUTE, minute);
        set(SECOND, second);
    }
    
    public final void clear() {
        for (int i = 0; i < fields.length; ) {
            stamp[i] = fields[i] = 0;
            isSet[i++] = false;
        }
        areAllFieldsSet = areFieldsSet = false;
        isTimeSet = false;
    }
    
    public final void clear(int field) {
        fields[field] = 0;
        stamp[field] = UNSET;
        isSet[field] = false;
        areAllFieldsSet = areFieldsSet = false;
        isTimeSet = false;
    }
    
    public final boolean isSet(int field) {
        return stamp[field] != UNSET;
    }
    
    protected void complete() {
        if (!isTimeSet) updateTime();
        if (!areFieldsSet || !areAllFieldsSet) {
            computeFields();
            areAllFieldsSet = areFieldsSet = true;
        } else {
            setFieldsComputed(ALL_FIELDS);
        }
    }
    
    final boolean isExternallySet(int field) {
        return stamp[field] >= MINIMUM_USER_STAMP;
    }
    
    final int getSetStateFields() {
        int mask = 0;
        for (int i = 0; i < fields.length; i++) {
            if (stamp[i] != UNSET) {
                mask |= 1 << i;
            }
        }
        return mask;
    }
    
    final void setFieldsComputed(int fieldMask) {
        if (fieldMask == ALL_FIELDS) {
            for (int i = 0; i < fields.length; i++) {
                stamp[i] = COMPUTED;
                isSet[i] = true;
            }
            areFieldsSet = areAllFieldsSet = true;
        } else {
            for (int i = 0; i < fields.length; i++) {
                if ((fieldMask & 1) == 1) {
                    stamp[i] = COMPUTED;
                    isSet[i] = true;
                } else {
                    if (areAllFieldsSet && !isSet[i]) {
                        areAllFieldsSet = false;
                    }
                }
                fieldMask >>>= 1;
            }
        }
    }
    
    final void setFieldsNormalized(int fieldMask) {
        if (fieldMask == ALL_FIELDS) {
            areFieldsSet = areAllFieldsSet = true;
            return;
        }
        for (int i = 0; i < fields.length; i++) {
            if ((fieldMask & 1) == 0) {
                stamp[i] = fields[i] = 0;
                isSet[i] = false;
            }
            fieldMask >>= 1;
        }
        areFieldsSet = true;
        areAllFieldsSet = false;
    }
    
    final boolean isPartiallyNormalized() {
        return areFieldsSet && !areAllFieldsSet;
    }
    
    final boolean isFullyNormalized() {
        return areFieldsSet && areAllFieldsSet;
    }
    
    final void setUnnormalized() {
        areFieldsSet = areAllFieldsSet = false;
    }
    
    static final boolean isFieldSet(int fieldMask, int field) {
        return (fieldMask & (1 << field)) != 0;
    }
    
    final int selectFields() {
        int fieldMask = YEAR_MASK;
        if (stamp[ERA] != UNSET) {
            fieldMask |= ERA_MASK;
        }
        int dowStamp = stamp[DAY_OF_WEEK];
        int monthStamp = stamp[MONTH];
        int domStamp = stamp[DAY_OF_MONTH];
        int womStamp = aggregateStamp(stamp[WEEK_OF_MONTH], dowStamp);
        int dowimStamp = aggregateStamp(stamp[DAY_OF_WEEK_IN_MONTH], dowStamp);
        int doyStamp = stamp[DAY_OF_YEAR];
        int woyStamp = aggregateStamp(stamp[WEEK_OF_YEAR], dowStamp);
        int bestStamp = domStamp;
        if (womStamp > bestStamp) {
            bestStamp = womStamp;
        }
        if (dowimStamp > bestStamp) {
            bestStamp = dowimStamp;
        }
        if (doyStamp > bestStamp) {
            bestStamp = doyStamp;
        }
        if (woyStamp > bestStamp) {
            bestStamp = woyStamp;
        }
        if (bestStamp == UNSET) {
            womStamp = stamp[WEEK_OF_MONTH];
            dowimStamp = Math.max(stamp[DAY_OF_WEEK_IN_MONTH], dowStamp);
            woyStamp = stamp[WEEK_OF_YEAR];
            bestStamp = Math.max(Math.max(womStamp, dowimStamp), woyStamp);
            if (bestStamp == UNSET) {
                bestStamp = domStamp = monthStamp;
            }
        }
        if (bestStamp == domStamp || (bestStamp == womStamp && stamp[WEEK_OF_MONTH] >= stamp[WEEK_OF_YEAR]) || (bestStamp == dowimStamp && stamp[DAY_OF_WEEK_IN_MONTH] >= stamp[WEEK_OF_YEAR])) {
            fieldMask |= MONTH_MASK;
            if (bestStamp == domStamp) {
                fieldMask |= DAY_OF_MONTH_MASK;
            } else {
                if (!$assertionsDisabled && !(bestStamp == womStamp || bestStamp == dowimStamp)) throw new AssertionError();
                if (dowStamp != UNSET) {
                    fieldMask |= DAY_OF_WEEK_MASK;
                }
                if (bestStamp == womStamp) {
                    fieldMask |= WEEK_OF_MONTH_MASK;
                } else {
                    if (!$assertionsDisabled && !(bestStamp == dowimStamp)) throw new AssertionError();
                    if (stamp[DAY_OF_WEEK_IN_MONTH] != UNSET) {
                        fieldMask |= DAY_OF_WEEK_IN_MONTH_MASK;
                    }
                }
            }
        } else {
            if (!$assertionsDisabled && !(bestStamp == doyStamp || bestStamp == woyStamp || bestStamp == UNSET)) throw new AssertionError();
            if (bestStamp == doyStamp) {
                fieldMask |= DAY_OF_YEAR_MASK;
            } else {
                if (!$assertionsDisabled && !(bestStamp == woyStamp)) throw new AssertionError();
                if (dowStamp != UNSET) {
                    fieldMask |= DAY_OF_WEEK_MASK;
                }
                fieldMask |= WEEK_OF_YEAR_MASK;
            }
        }
        int hourOfDayStamp = stamp[HOUR_OF_DAY];
        int hourStamp = aggregateStamp(stamp[HOUR], stamp[AM_PM]);
        bestStamp = (hourStamp > hourOfDayStamp) ? hourStamp : hourOfDayStamp;
        if (bestStamp == UNSET) {
            bestStamp = Math.max(stamp[HOUR], stamp[AM_PM]);
        }
        if (bestStamp != UNSET) {
            if (bestStamp == hourOfDayStamp) {
                fieldMask |= HOUR_OF_DAY_MASK;
            } else {
                fieldMask |= HOUR_MASK;
                if (stamp[AM_PM] != UNSET) {
                    fieldMask |= AM_PM_MASK;
                }
            }
        }
        if (stamp[MINUTE] != UNSET) {
            fieldMask |= MINUTE_MASK;
        }
        if (stamp[SECOND] != UNSET) {
            fieldMask |= SECOND_MASK;
        }
        if (stamp[MILLISECOND] != UNSET) {
            fieldMask |= MILLISECOND_MASK;
        }
        if (stamp[ZONE_OFFSET] >= MINIMUM_USER_STAMP) {
            fieldMask |= ZONE_OFFSET_MASK;
        }
        if (stamp[DST_OFFSET] >= MINIMUM_USER_STAMP) {
            fieldMask |= DST_OFFSET_MASK;
        }
        return fieldMask;
    }
    
    private static final int aggregateStamp(int stamp_a, int stamp_b) {
        if (stamp_a == UNSET || stamp_b == UNSET) {
            return UNSET;
        }
        return (stamp_a > stamp_b) ? stamp_a : stamp_b;
    }
    
    public boolean equals(Object obj) {
        if (this == obj) return true;
        try {
            Calendar that = (Calendar)(Calendar)obj;
            return compareTo(getMillisOf(that)) == 0 && lenient == that.lenient && firstDayOfWeek == that.firstDayOfWeek && minimalDaysInFirstWeek == that.minimalDaysInFirstWeek && zone.equals(that.zone);
        } catch (Exception e) {
        }
        return false;
    }
    
    public int hashCode() {
        int otheritems = (lenient ? 1 : 0) | (firstDayOfWeek << 1) | (minimalDaysInFirstWeek << 4) | (zone.hashCode() << 7);
        long t = getMillisOf(this);
        return (int)t ^ (int)(t >> 32) ^ otheritems;
    }
    
    public boolean before(Object when) {
        return when instanceof Calendar && compareTo((Calendar)(Calendar)when) < 0;
    }
    
    public boolean after(Object when) {
        return when instanceof Calendar && compareTo((Calendar)(Calendar)when) > 0;
    }
    
    public int compareTo(Calendar anotherCalendar) {
        return compareTo(getMillisOf(anotherCalendar));
    }
    
    public abstract void add(int field, int amount);
    
    public abstract void roll(int field, boolean up);
    
    public void roll(int field, int amount) {
        while (amount > 0) {
            roll(field, true);
            amount--;
        }
        while (amount < 0) {
            roll(field, false);
            amount++;
        }
    }
    
    public void setTimeZone(TimeZone value) {
        zone = value;
        sharedZone = false;
        areAllFieldsSet = areFieldsSet = false;
    }
    
    public TimeZone getTimeZone() {
        if (sharedZone) {
            zone = (TimeZone)(TimeZone)zone.clone();
            sharedZone = false;
        }
        return zone;
    }
    
    TimeZone getZone() {
        return zone;
    }
    
    void setZoneShared(boolean shared) {
        sharedZone = shared;
    }
    
    public void setLenient(boolean lenient) {
        this.lenient = lenient;
    }
    
    public boolean isLenient() {
        return lenient;
    }
    
    public void setFirstDayOfWeek(int value) {
        if (firstDayOfWeek == value) {
            return;
        }
        firstDayOfWeek = value;
        invalidateWeekFields();
    }
    
    public int getFirstDayOfWeek() {
        return firstDayOfWeek;
    }
    
    public void setMinimalDaysInFirstWeek(int value) {
        if (minimalDaysInFirstWeek == value) {
            return;
        }
        minimalDaysInFirstWeek = value;
        invalidateWeekFields();
    }
    
    public int getMinimalDaysInFirstWeek() {
        return minimalDaysInFirstWeek;
    }
    
    public abstract int getMinimum(int field);
    
    public abstract int getMaximum(int field);
    
    public abstract int getGreatestMinimum(int field);
    
    public abstract int getLeastMaximum(int field);
    
    public int getActualMinimum(int field) {
        int fieldValue = getGreatestMinimum(field);
        int endValue = getMinimum(field);
        if (fieldValue == endValue) {
            return fieldValue;
        }
        Calendar work = (Calendar)(Calendar)this.clone();
        work.setLenient(true);
        int result = fieldValue;
        do {
            work.set(field, fieldValue);
            if (work.get(field) != fieldValue) {
                break;
            } else {
                result = fieldValue;
                fieldValue--;
            }
        }         while (fieldValue >= endValue);
        return result;
    }
    
    public int getActualMaximum(int field) {
        int fieldValue = getLeastMaximum(field);
        int endValue = getMaximum(field);
        if (fieldValue == endValue) {
            return fieldValue;
        }
        Calendar work = (Calendar)(Calendar)this.clone();
        work.setLenient(true);
        if (field == WEEK_OF_YEAR || field == WEEK_OF_MONTH) work.set(DAY_OF_WEEK, firstDayOfWeek);
        int result = fieldValue;
        do {
            work.set(field, fieldValue);
            if (work.get(field) != fieldValue) {
                break;
            } else {
                result = fieldValue;
                fieldValue++;
            }
        }         while (fieldValue <= endValue);
        return result;
    }
    
    public Object clone() {
        try {
            Calendar other = (Calendar)(Calendar)super.clone();
            other.fields = new int[FIELD_COUNT];
            other.isSet = new boolean[FIELD_COUNT];
            other.stamp = new int[FIELD_COUNT];
            for (int i = 0; i < FIELD_COUNT; i++) {
                other.fields[i] = fields[i];
                other.stamp[i] = stamp[i];
                other.isSet[i] = isSet[i];
            }
            other.zone = (TimeZone)(TimeZone)zone.clone();
            return other;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    private static final String[] FIELD_NAME = {"ERA", "YEAR", "MONTH", "WEEK_OF_YEAR", "WEEK_OF_MONTH", "DAY_OF_MONTH", "DAY_OF_YEAR", "DAY_OF_WEEK", "DAY_OF_WEEK_IN_MONTH", "AM_PM", "HOUR", "HOUR_OF_DAY", "MINUTE", "SECOND", "MILLISECOND", "ZONE_OFFSET", "DST_OFFSET"};
    
    static final String getFieldName(int field) {
        return FIELD_NAME[field];
    }
    
    public String toString() {
        StringBuilder buffer = new StringBuilder(800);
        buffer.append(getClass().getName()).append('[');
        appendValue(buffer, "time", isTimeSet, time);
        buffer.append(",areFieldsSet=").append(areFieldsSet);
        buffer.append(",areAllFieldsSet=").append(areAllFieldsSet);
        buffer.append(",lenient=").append(lenient);
        buffer.append(",zone=").append(zone);
        appendValue(buffer, ",firstDayOfWeek", true, (long)firstDayOfWeek);
        appendValue(buffer, ",minimalDaysInFirstWeek", true, (long)minimalDaysInFirstWeek);
        for (int i = 0; i < FIELD_COUNT; ++i) {
            buffer.append(',');
            appendValue(buffer, FIELD_NAME[i], isSet(i), (long)fields[i]);
        }
        buffer.append(']');
        return buffer.toString();
    }
    
    private static final void appendValue(StringBuilder sb, String item, boolean valid, long value) {
        sb.append(item).append('=');
        if (valid) {
            sb.append(value);
        } else {
            sb.append('?');
        }
    }
    
    private void setWeekCountData(Locale desiredLocale) {
        int[] data = (int[])cachedLocaleData.get(desiredLocale);
        if (data == null) {
            ResourceBundle resource = LocaleData.getLocaleElements(desiredLocale);
            String[] dateTimePatterns = resource.getStringArray("DateTimeElements");
            data = new int[2];
            data[0] = Integer.parseInt(dateTimePatterns[0]);
            data[1] = Integer.parseInt(dateTimePatterns[1]);
            cachedLocaleData.put(desiredLocale, data);
        }
        firstDayOfWeek = data[0];
        minimalDaysInFirstWeek = data[1];
    }
    
    private void updateTime() {
        computeTime();
        isTimeSet = true;
    }
    
    private int compareTo(long t) {
        long thisTime = getMillisOf(this);
        return (thisTime > t) ? 1 : (thisTime == t) ? 0 : -1;
    }
    
    private static final long getMillisOf(Calendar calendar) {
        if (calendar.isTimeSet) {
            return calendar.time;
        }
        Calendar cal = (Calendar)(Calendar)calendar.clone();
        cal.setLenient(true);
        return cal.getTimeInMillis();
    }
    
    private final void adjustStamp() {
        int max = MINIMUM_USER_STAMP;
        int newStamp = MINIMUM_USER_STAMP;
        for (; ; ) {
            int min = Integer.MAX_VALUE;
            for (int i = 0; i < stamp.length; i++) {
                int v = stamp[i];
                if (v >= newStamp && min > v) {
                    min = v;
                }
                if (max < v) {
                    max = v;
                }
            }
            if (max != min && min == Integer.MAX_VALUE) {
                break;
            }
            for (int i = 0; i < stamp.length; i++) {
                if (stamp[i] == min) {
                    stamp[i] = newStamp;
                }
            }
            newStamp++;
            if (min == max) {
                break;
            }
        }
        nextStamp = newStamp;
    }
    
    private void invalidateWeekFields() {
        if (stamp[WEEK_OF_MONTH] != COMPUTED && stamp[WEEK_OF_YEAR] != COMPUTED) {
            return;
        }
        Calendar cal = (Calendar)(Calendar)clone();
        cal.setLenient(true);
        cal.clear(WEEK_OF_MONTH);
        cal.clear(WEEK_OF_YEAR);
        if (stamp[WEEK_OF_MONTH] == COMPUTED) {
            int weekOfMonth = cal.get(WEEK_OF_MONTH);
            if (fields[WEEK_OF_MONTH] != weekOfMonth) {
                fields[WEEK_OF_MONTH] = weekOfMonth;
            }
        }
        if (stamp[WEEK_OF_YEAR] == COMPUTED) {
            int weekOfYear = cal.get(WEEK_OF_YEAR);
            if (fields[WEEK_OF_YEAR] != weekOfYear) {
                fields[WEEK_OF_YEAR] = weekOfYear;
            }
        }
    }
    
    private void writeObject(ObjectOutputStream stream) throws IOException {
        if (!isTimeSet) {
            try {
                updateTime();
            } catch (IllegalArgumentException e) {
            }
        }
        TimeZone savedZone = null;
        if (zone instanceof ZoneInfo) {
            SimpleTimeZone stz = ((ZoneInfo)(ZoneInfo)zone).getLastRuleInstance();
            if (stz == null) {
                stz = new SimpleTimeZone(zone.getRawOffset(), zone.getID());
            }
            savedZone = zone;
            zone = stz;
        }
        stream.defaultWriteObject();
        stream.writeObject(savedZone);
        if (savedZone != null) {
            zone = savedZone;
        }
    }
    {
    }
    
    private void readObject(ObjectInputStream stream) throws IOException, ClassNotFoundException {
        final ObjectInputStream input = stream;
        input.defaultReadObject();
        stamp = new int[FIELD_COUNT];
        if (serialVersionOnStream >= 2) {
            isTimeSet = true;
            if (fields == null) fields = new int[FIELD_COUNT];
            if (isSet == null) isSet = new boolean[FIELD_COUNT];
        } else if (serialVersionOnStream >= 0) {
            for (int i = 0; i < FIELD_COUNT; ++i) stamp[i] = isSet[i] ? COMPUTED : UNSET;
        }
        serialVersionOnStream = currentSerialVersion;
        ZoneInfo zi = null;
        try {
            zi = (ZoneInfo)AccessController.doPrivileged(new Calendar$1(this, input), Calendar$CalendarAccessControlContext.access$000());
        } catch (PrivilegedActionException pae) {
            Exception e = pae.getException();
            if (!(e instanceof OptionalDataException)) {
                if (e instanceof RuntimeException) {
                    throw (RuntimeException)(RuntimeException)e;
                } else if (e instanceof IOException) {
                    throw (IOException)(IOException)e;
                } else if (e instanceof ClassNotFoundException) {
                    throw (ClassNotFoundException)(ClassNotFoundException)e;
                }
                throw new RuntimeException(e);
            }
        }
        if (zi != null) {
            zone = zi;
        }
        if (zone instanceof SimpleTimeZone) {
            String id = zone.getID();
            TimeZone tz = TimeZone.getTimeZone(id);
            if (tz != null && tz.hasSameRules(zone) && tz.getID().equals(id)) {
                zone = tz;
            }
        }
    }
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((Calendar)x0);
    }
}
