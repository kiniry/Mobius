package java.text;

import java.util.Locale;
import java.util.MissingResourceException;
import java.util.TimeZone;
import java.util.Calendar;
import java.util.Date;
import sun.text.resources.LocaleData;

public abstract class DateFormat extends Format {
    protected Calendar calendar;
    protected NumberFormat numberFormat;
    public static final int ERA_FIELD = 0;
    public static final int YEAR_FIELD = 1;
    public static final int MONTH_FIELD = 2;
    public static final int DATE_FIELD = 3;
    public static final int HOUR_OF_DAY1_FIELD = 4;
    public static final int HOUR_OF_DAY0_FIELD = 5;
    public static final int MINUTE_FIELD = 6;
    public static final int SECOND_FIELD = 7;
    public static final int MILLISECOND_FIELD = 8;
    public static final int DAY_OF_WEEK_FIELD = 9;
    public static final int DAY_OF_YEAR_FIELD = 10;
    public static final int DAY_OF_WEEK_IN_MONTH_FIELD = 11;
    public static final int WEEK_OF_YEAR_FIELD = 12;
    public static final int WEEK_OF_MONTH_FIELD = 13;
    public static final int AM_PM_FIELD = 14;
    public static final int HOUR1_FIELD = 15;
    public static final int HOUR0_FIELD = 16;
    public static final int TIMEZONE_FIELD = 17;
    private static final long serialVersionUID = 7218322306649953788L;
    
    public final StringBuffer format(Object obj, StringBuffer toAppendTo, FieldPosition fieldPosition) {
        if (obj instanceof Date) return format((Date)(Date)obj, toAppendTo, fieldPosition); else if (obj instanceof Number) return format(new Date(((Number)(Number)obj).longValue()), toAppendTo, fieldPosition); else throw new IllegalArgumentException("Cannot format given Object as a Date");
    }
    
    public abstract StringBuffer format(Date date, StringBuffer toAppendTo, FieldPosition fieldPosition);
    
    public final String format(Date date) {
        return format(date, new StringBuffer(), DontCareFieldPosition.INSTANCE).toString();
    }
    
    public Date parse(String source) throws ParseException {
        ParsePosition pos = new ParsePosition(0);
        Date result = parse(source, pos);
        if (pos.index == 0) throw new ParseException("Unparseable date: \"" + source + "\"", pos.errorIndex);
        return result;
    }
    
    public abstract Date parse(String source, ParsePosition pos);
    
    public Object parseObject(String source, ParsePosition pos) {
        return parse(source, pos);
    }
    public static final int FULL = 0;
    public static final int LONG = 1;
    public static final int MEDIUM = 2;
    public static final int SHORT = 3;
    public static final int DEFAULT = MEDIUM;
    
    public static final DateFormat getTimeInstance() {
        return get(DEFAULT, 0, 1, Locale.getDefault());
    }
    
    public static final DateFormat getTimeInstance(int style) {
        return get(style, 0, 1, Locale.getDefault());
    }
    
    public static final DateFormat getTimeInstance(int style, Locale aLocale) {
        return get(style, 0, 1, aLocale);
    }
    
    public static final DateFormat getDateInstance() {
        return get(0, DEFAULT, 2, Locale.getDefault());
    }
    
    public static final DateFormat getDateInstance(int style) {
        return get(0, style, 2, Locale.getDefault());
    }
    
    public static final DateFormat getDateInstance(int style, Locale aLocale) {
        return get(0, style, 2, aLocale);
    }
    
    public static final DateFormat getDateTimeInstance() {
        return get(DEFAULT, DEFAULT, 3, Locale.getDefault());
    }
    
    public static final DateFormat getDateTimeInstance(int dateStyle, int timeStyle) {
        return get(timeStyle, dateStyle, 3, Locale.getDefault());
    }
    
    public static final DateFormat getDateTimeInstance(int dateStyle, int timeStyle, Locale aLocale) {
        return get(timeStyle, dateStyle, 3, aLocale);
    }
    
    public static final DateFormat getInstance() {
        return getDateTimeInstance(SHORT, SHORT);
    }
    
    public static Locale[] getAvailableLocales() {
        return LocaleData.getAvailableLocales("DateTimePatterns");
    }
    
    public void setCalendar(Calendar newCalendar) {
        this.calendar = newCalendar;
    }
    
    public Calendar getCalendar() {
        return calendar;
    }
    
    public void setNumberFormat(NumberFormat newNumberFormat) {
        this.numberFormat = newNumberFormat;
    }
    
    public NumberFormat getNumberFormat() {
        return numberFormat;
    }
    
    public void setTimeZone(TimeZone zone) {
        calendar.setTimeZone(zone);
    }
    
    public TimeZone getTimeZone() {
        return calendar.getTimeZone();
    }
    
    public void setLenient(boolean lenient) {
        calendar.setLenient(lenient);
    }
    
    public boolean isLenient() {
        return calendar.isLenient();
    }
    
    public int hashCode() {
        return numberFormat.hashCode();
    }
    
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        DateFormat other = (DateFormat)(DateFormat)obj;
        return (calendar.getFirstDayOfWeek() == other.calendar.getFirstDayOfWeek() && calendar.getMinimalDaysInFirstWeek() == other.calendar.getMinimalDaysInFirstWeek() && calendar.isLenient() == other.calendar.isLenient() && calendar.getTimeZone().equals(other.calendar.getTimeZone()) && numberFormat.equals(other.numberFormat));
    }
    
    public Object clone() {
        DateFormat other = (DateFormat)(DateFormat)super.clone();
        other.calendar = (Calendar)(Calendar)calendar.clone();
        other.numberFormat = (NumberFormat)(NumberFormat)numberFormat.clone();
        return other;
    }
    
    private static DateFormat get(int timeStyle, int dateStyle, int flags, Locale loc) {
        if ((flags & 1) != 0) {
            if (timeStyle < 0 || timeStyle > 3) {
                throw new IllegalArgumentException("Illegal time style " + timeStyle);
            }
        } else {
            timeStyle = -1;
        }
        if ((flags & 2) != 0) {
            if (dateStyle < 0 || dateStyle > 3) {
                throw new IllegalArgumentException("Illegal date style " + dateStyle);
            }
        } else {
            dateStyle = -1;
        }
        try {
            return new SimpleDateFormat(timeStyle, dateStyle, loc);
        } catch (MissingResourceException e) {
            return new SimpleDateFormat("M/d/yy h:mm a");
        }
    }
    
    protected DateFormat() {
        
    }
    {
    }
}
