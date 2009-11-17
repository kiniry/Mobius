package java.text;

import java.io.InvalidObjectException;
import java.util.HashMap;
import java.util.Map;
import java.util.Calendar;

public class DateFormat$Field extends Format$Field {
    private static final long serialVersionUID = 7441350119349544720L;
    private static final Map instanceMap = new HashMap(18);
    private static final DateFormat$Field[] calendarToFieldMapping = new DateFormat$Field[Calendar.FIELD_COUNT];
    private int calendarField;
    
    public static DateFormat$Field ofCalendarField(int calendarField) {
        if (calendarField < 0 || calendarField >= calendarToFieldMapping.length) {
            throw new IllegalArgumentException("Unknown Calendar constant " + calendarField);
        }
        return calendarToFieldMapping[calendarField];
    }
    
    protected DateFormat$Field(String name, int calendarField) {
        super(name);
        this.calendarField = calendarField;
        if (this.getClass() == DateFormat.Field.class) {
            instanceMap.put(name, this);
            if (calendarField >= 0) {
                calendarToFieldMapping[calendarField] = this;
            }
        }
    }
    
    public int getCalendarField() {
        return calendarField;
    }
    
    protected Object readResolve() throws InvalidObjectException {
        if (this.getClass() != DateFormat.Field.class) {
            throw new InvalidObjectException("subclass didn\'t correctly implement readResolve");
        }
        Object instance = instanceMap.get(getName());
        if (instance != null) {
            return instance;
        } else {
            throw new InvalidObjectException("unknown attribute name");
        }
    }
    public static final DateFormat$Field ERA = new DateFormat$Field("era", Calendar.ERA);
    public static final DateFormat$Field YEAR = new DateFormat$Field("year", Calendar.YEAR);
    public static final DateFormat$Field MONTH = new DateFormat$Field("month", Calendar.MONTH);
    public static final DateFormat$Field DAY_OF_MONTH = new DateFormat$Field("day of month", Calendar.DAY_OF_MONTH);
    public static final DateFormat$Field HOUR_OF_DAY1 = new DateFormat$Field("hour of day 1", -1);
    public static final DateFormat$Field HOUR_OF_DAY0 = new DateFormat$Field("hour of day", Calendar.HOUR_OF_DAY);
    public static final DateFormat$Field MINUTE = new DateFormat$Field("minute", Calendar.MINUTE);
    public static final DateFormat$Field SECOND = new DateFormat$Field("second", Calendar.SECOND);
    public static final DateFormat$Field MILLISECOND = new DateFormat$Field("millisecond", Calendar.MILLISECOND);
    public static final DateFormat$Field DAY_OF_WEEK = new DateFormat$Field("day of week", Calendar.DAY_OF_WEEK);
    public static final DateFormat$Field DAY_OF_YEAR = new DateFormat$Field("day of year", Calendar.DAY_OF_YEAR);
    public static final DateFormat$Field DAY_OF_WEEK_IN_MONTH = new DateFormat$Field("day of week in month", Calendar.DAY_OF_WEEK_IN_MONTH);
    public static final DateFormat$Field WEEK_OF_YEAR = new DateFormat$Field("week of year", Calendar.WEEK_OF_YEAR);
    public static final DateFormat$Field WEEK_OF_MONTH = new DateFormat$Field("week of month", Calendar.WEEK_OF_MONTH);
    public static final DateFormat$Field AM_PM = new DateFormat$Field("am pm", Calendar.AM_PM);
    public static final DateFormat$Field HOUR1 = new DateFormat$Field("hour 1", -1);
    public static final DateFormat$Field HOUR0 = new DateFormat$Field("hour", Calendar.HOUR);
    public static final DateFormat$Field TIME_ZONE = new DateFormat$Field("time zone", -1);
}
