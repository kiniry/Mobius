package java.text;

import java.util.TimeZone;
import java.util.Calendar;
import java.util.Date;
import java.util.Locale;
import java.util.ResourceBundle;
import java.util.SimpleTimeZone;
import java.io.ObjectInputStream;
import java.io.InvalidObjectException;
import java.io.IOException;
import java.lang.ClassNotFoundException;
import java.util.Hashtable;
import java.lang.StringIndexOutOfBoundsException;
import sun.text.resources.LocaleData;
import sun.util.calendar.CalendarUtils;
import sun.util.calendar.ZoneInfoFile;

public class SimpleDateFormat extends DateFormat {
    static final long serialVersionUID = 4774881970558875024L;
    static final int currentSerialVersion = 1;
    private int serialVersionOnStream = currentSerialVersion;
    private String pattern;
    private transient char[] compiledPattern;
    private static final int TAG_QUOTE_ASCII_CHAR = 100;
    private static final int TAG_QUOTE_CHARS = 101;
    private transient char zeroDigit;
    private DateFormatSymbols formatData;
    private Date defaultCenturyStart;
    private transient int defaultCenturyStartYear;
    private static final int millisPerHour = 60 * 60 * 1000;
    private static final int millisPerMinute = 60 * 1000;
    private static final String GMT = "GMT";
    private static Hashtable cachedLocaleData = new Hashtable(3);
    private static Hashtable cachedNumberFormatData = new Hashtable(3);
    
    public SimpleDateFormat() {
        this(SHORT, SHORT, Locale.getDefault());
    }
    
    public SimpleDateFormat(String pattern) {
        this(pattern, Locale.getDefault());
    }
    
    public SimpleDateFormat(String pattern, Locale locale) {
        
        this.pattern = pattern;
        this.formatData = new DateFormatSymbols(locale);
        initialize(locale);
    }
    
    public SimpleDateFormat(String pattern, DateFormatSymbols formatSymbols) {
        
        this.pattern = pattern;
        this.formatData = (DateFormatSymbols)(DateFormatSymbols)formatSymbols.clone();
        initialize(Locale.getDefault());
    }
    
    SimpleDateFormat(int timeStyle, int dateStyle, Locale loc) {
        
        String[] dateTimePatterns = (String[])(String[])cachedLocaleData.get(loc);
        if (dateTimePatterns == null) {
            ResourceBundle r = LocaleData.getLocaleElements(loc);
            dateTimePatterns = r.getStringArray("DateTimePatterns");
            cachedLocaleData.put(loc, dateTimePatterns);
        }
        formatData = new DateFormatSymbols(loc);
        if ((timeStyle >= 0) && (dateStyle >= 0)) {
            Object[] dateTimeArgs = {dateTimePatterns[timeStyle], dateTimePatterns[dateStyle + 4]};
            pattern = MessageFormat.format(dateTimePatterns[8], dateTimeArgs);
        } else if (timeStyle >= 0) {
            pattern = dateTimePatterns[timeStyle];
        } else if (dateStyle >= 0) {
            pattern = dateTimePatterns[dateStyle + 4];
        } else {
            throw new IllegalArgumentException("No date or time style specified");
        }
        initialize(loc);
    }
    
    private void initialize(Locale loc) {
        compiledPattern = compile(pattern);
        calendar = Calendar.getInstance(TimeZone.getDefault(), loc);
        numberFormat = (NumberFormat)(NumberFormat)cachedNumberFormatData.get(loc);
        if (numberFormat == null) {
            numberFormat = NumberFormat.getIntegerInstance(loc);
            numberFormat.setGroupingUsed(false);
            cachedNumberFormatData.put(loc, numberFormat);
        }
        numberFormat = (NumberFormat)(NumberFormat)numberFormat.clone();
        initializeDefaultCentury();
    }
    
    private char[] compile(String pattern) {
        int length = pattern.length();
        boolean inQuote = false;
        StringBuilder compiledPattern = new StringBuilder(length * 2);
        StringBuilder tmpBuffer = null;
        int count = 0;
        int lastTag = -1;
        for (int i = 0; i < length; i++) {
            char c = pattern.charAt(i);
            if (c == '\'') {
                if ((i + 1) < length) {
                    c = pattern.charAt(i + 1);
                    if (c == '\'') {
                        i++;
                        if (count != 0) {
                            encode(lastTag, count, compiledPattern);
                            lastTag = -1;
                            count = 0;
                        }
                        if (inQuote) {
                            tmpBuffer.append(c);
                        } else {
                            compiledPattern.append((char)(TAG_QUOTE_ASCII_CHAR << 8 | c));
                        }
                        continue;
                    }
                }
                if (!inQuote) {
                    if (count != 0) {
                        encode(lastTag, count, compiledPattern);
                        lastTag = -1;
                        count = 0;
                    }
                    if (tmpBuffer == null) {
                        tmpBuffer = new StringBuilder(length);
                    } else {
                        tmpBuffer.setLength(0);
                    }
                    inQuote = true;
                } else {
                    int len = tmpBuffer.length();
                    if (len == 1) {
                        char ch = tmpBuffer.charAt(0);
                        if (ch < 128) {
                            compiledPattern.append((char)(TAG_QUOTE_ASCII_CHAR << 8 | ch));
                        } else {
                            compiledPattern.append((char)(TAG_QUOTE_CHARS << 8 | 1));
                            compiledPattern.append(ch);
                        }
                    } else {
                        encode(TAG_QUOTE_CHARS, len, compiledPattern);
                        compiledPattern.append(tmpBuffer);
                    }
                    inQuote = false;
                }
                continue;
            }
            if (inQuote) {
                tmpBuffer.append(c);
                continue;
            }
            if (!(c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z')) {
                if (count != 0) {
                    encode(lastTag, count, compiledPattern);
                    lastTag = -1;
                    count = 0;
                }
                if (c < 128) {
                    compiledPattern.append((char)(TAG_QUOTE_ASCII_CHAR << 8 | c));
                } else {
                    int j;
                    for (j = i + 1; j < length; j++) {
                        char d = pattern.charAt(j);
                        if (d == '\'' || (d >= 'a' && d <= 'z' || d >= 'A' && d <= 'Z')) {
                            break;
                        }
                    }
                    compiledPattern.append((char)(TAG_QUOTE_CHARS << 8 | (j - i)));
                    for (; i < j; i++) {
                        compiledPattern.append(pattern.charAt(i));
                    }
                    i--;
                }
                continue;
            }
            int tag;
            if ((tag = formatData.patternChars.indexOf(c)) == -1) {
                throw new IllegalArgumentException("Illegal pattern character " + "\'" + c + "\'");
            }
            if (lastTag == -1 || lastTag == tag) {
                lastTag = tag;
                count++;
                continue;
            }
            encode(lastTag, count, compiledPattern);
            lastTag = tag;
            count = 1;
        }
        if (inQuote) {
            throw new IllegalArgumentException("Unterminated quote");
        }
        if (count != 0) {
            encode(lastTag, count, compiledPattern);
        }
        int len = compiledPattern.length();
        char[] r = new char[len];
        compiledPattern.getChars(0, len, r, 0);
        return r;
    }
    
    private static final void encode(int tag, int length, StringBuilder buffer) {
        if (length < 255) {
            buffer.append((char)(tag << 8 | length));
        } else {
            buffer.append((char)((tag << 8) | 255));
            buffer.append((char)(length >>> 16));
            buffer.append((char)(length & 65535));
        }
    }
    
    private void initializeDefaultCentury() {
        calendar.setTime(new Date());
        calendar.add(Calendar.YEAR, -80);
        parseAmbiguousDatesAsAfter(calendar.getTime());
    }
    
    private void parseAmbiguousDatesAsAfter(Date startDate) {
        defaultCenturyStart = startDate;
        calendar.setTime(startDate);
        defaultCenturyStartYear = calendar.get(Calendar.YEAR);
    }
    
    public void set2DigitYearStart(Date startDate) {
        parseAmbiguousDatesAsAfter(startDate);
    }
    
    public Date get2DigitYearStart() {
        return defaultCenturyStart;
    }
    
    public StringBuffer format(Date date, StringBuffer toAppendTo, FieldPosition pos) {
        pos.beginIndex = pos.endIndex = 0;
        return format(date, toAppendTo, pos.getFieldDelegate());
    }
    
    private StringBuffer format(Date date, StringBuffer toAppendTo, Format$FieldDelegate delegate) {
        calendar.setTime(date);
        for (int i = 0; i < compiledPattern.length; ) {
            int tag = compiledPattern[i] >>> 8;
            int count = compiledPattern[i++] & 255;
            if (count == 255) {
                count = compiledPattern[i++] << 16;
                count |= compiledPattern[i++];
            }
            switch (tag) {
            case TAG_QUOTE_ASCII_CHAR: 
                toAppendTo.append((char)count);
                break;
            
            case TAG_QUOTE_CHARS: 
                toAppendTo.append(compiledPattern, i, count);
                i += count;
                break;
            
            default: 
                subFormat(tag, count, delegate, toAppendTo);
                break;
            
            }
        }
        return toAppendTo;
    }
    
    public AttributedCharacterIterator formatToCharacterIterator(Object obj) {
        StringBuffer sb = new StringBuffer();
        CharacterIteratorFieldDelegate delegate = new CharacterIteratorFieldDelegate();
        if (obj instanceof Date) {
            format((Date)(Date)obj, sb, delegate);
        } else if (obj instanceof Number) {
            format(new Date(((Number)(Number)obj).longValue()), sb, delegate);
        } else if (obj == null) {
            throw new NullPointerException("formatToCharacterIterator must be passed non-null object");
        } else {
            throw new IllegalArgumentException("Cannot format given Object as a Date");
        }
        return delegate.getIterator(sb.toString());
    }
    private static final int[] PATTERN_INDEX_TO_CALENDAR_FIELD = {Calendar.ERA, Calendar.YEAR, Calendar.MONTH, Calendar.DATE, Calendar.HOUR_OF_DAY, Calendar.HOUR_OF_DAY, Calendar.MINUTE, Calendar.SECOND, Calendar.MILLISECOND, Calendar.DAY_OF_WEEK, Calendar.DAY_OF_YEAR, Calendar.DAY_OF_WEEK_IN_MONTH, Calendar.WEEK_OF_YEAR, Calendar.WEEK_OF_MONTH, Calendar.AM_PM, Calendar.HOUR, Calendar.HOUR, Calendar.ZONE_OFFSET, Calendar.ZONE_OFFSET};
    private static final int[] PATTERN_INDEX_TO_DATE_FORMAT_FIELD = {DateFormat.ERA_FIELD, DateFormat.YEAR_FIELD, DateFormat.MONTH_FIELD, DateFormat.DATE_FIELD, DateFormat.HOUR_OF_DAY1_FIELD, DateFormat.HOUR_OF_DAY0_FIELD, DateFormat.MINUTE_FIELD, DateFormat.SECOND_FIELD, DateFormat.MILLISECOND_FIELD, DateFormat.DAY_OF_WEEK_FIELD, DateFormat.DAY_OF_YEAR_FIELD, DateFormat.DAY_OF_WEEK_IN_MONTH_FIELD, DateFormat.WEEK_OF_YEAR_FIELD, DateFormat.WEEK_OF_MONTH_FIELD, DateFormat.AM_PM_FIELD, DateFormat.HOUR1_FIELD, DateFormat.HOUR0_FIELD, DateFormat.TIMEZONE_FIELD, DateFormat.TIMEZONE_FIELD};
    private static final DateFormat$Field[] PATTERN_INDEX_TO_DATE_FORMAT_FIELD_ID = {DateFormat$Field.ERA, DateFormat$Field.YEAR, DateFormat$Field.MONTH, DateFormat$Field.DAY_OF_MONTH, DateFormat$Field.HOUR_OF_DAY1, DateFormat$Field.HOUR_OF_DAY0, DateFormat$Field.MINUTE, DateFormat$Field.SECOND, DateFormat$Field.MILLISECOND, DateFormat$Field.DAY_OF_WEEK, DateFormat$Field.DAY_OF_YEAR, DateFormat$Field.DAY_OF_WEEK_IN_MONTH, DateFormat$Field.WEEK_OF_YEAR, DateFormat$Field.WEEK_OF_MONTH, DateFormat$Field.AM_PM, DateFormat$Field.HOUR1, DateFormat$Field.HOUR0, DateFormat$Field.TIME_ZONE, DateFormat$Field.TIME_ZONE};
    
    private void subFormat(int patternCharIndex, int count, Format$FieldDelegate delegate, StringBuffer buffer) {
        int maxIntCount = Integer.MAX_VALUE;
        String current = null;
        int beginOffset = buffer.length();
        int field = PATTERN_INDEX_TO_CALENDAR_FIELD[patternCharIndex];
        int value = calendar.get(field);
        switch (patternCharIndex) {
        case 0: 
            current = formatData.eras[value];
            break;
        
        case 1: 
            if (count >= 4) zeroPaddingNumber(value, count, maxIntCount, buffer); else zeroPaddingNumber(value, 2, 2, buffer);
            break;
        
        case 2: 
            if (count >= 4) current = formatData.months[value]; else if (count == 3) current = formatData.shortMonths[value]; else zeroPaddingNumber(value + 1, count, maxIntCount, buffer);
            break;
        
        case 4: 
            if (value == 0) zeroPaddingNumber(calendar.getMaximum(Calendar.HOUR_OF_DAY) + 1, count, maxIntCount, buffer); else zeroPaddingNumber(value, count, maxIntCount, buffer);
            break;
        
        case 9: 
            if (count >= 4) current = formatData.weekdays[value]; else current = formatData.shortWeekdays[value];
            break;
        
        case 14: 
            current = formatData.ampms[value];
            break;
        
        case 15: 
            if (value == 0) zeroPaddingNumber(calendar.getLeastMaximum(Calendar.HOUR) + 1, count, maxIntCount, buffer); else zeroPaddingNumber(value, count, maxIntCount, buffer);
            break;
        
        case 17: 
            int zoneIndex = formatData.getZoneIndex(calendar.getTimeZone().getID());
            if (zoneIndex == -1) {
                value = calendar.get(Calendar.ZONE_OFFSET) + calendar.get(Calendar.DST_OFFSET);
                buffer.append(ZoneInfoFile.toCustomID(value));
            } else {
                int index = (calendar.get(Calendar.DST_OFFSET) == 0) ? 1 : 3;
                if (count < 4) {
                    index++;
                }
                buffer.append(formatData.zoneStrings[zoneIndex][index]);
            }
            break;
        
        case 18: 
            value = (calendar.get(Calendar.ZONE_OFFSET) + calendar.get(Calendar.DST_OFFSET)) / 60000;
            int width = 4;
            if (value >= 0) {
                buffer.append('+');
            } else {
                width++;
            }
            int num = (value / 60) * 100 + (value % 60);
            CalendarUtils.sprintf0d(buffer, num, width);
            break;
        
        default: 
            zeroPaddingNumber(value, count, maxIntCount, buffer);
            break;
        
        }
        if (current != null) {
            buffer.append(current);
        }
        int fieldID = PATTERN_INDEX_TO_DATE_FORMAT_FIELD[patternCharIndex];
        DateFormat$Field f = PATTERN_INDEX_TO_DATE_FORMAT_FIELD_ID[patternCharIndex];
        delegate.formatted(fieldID, f, f, beginOffset, buffer.length(), buffer);
    }
    
    private final void zeroPaddingNumber(int value, int minDigits, int maxDigits, StringBuffer buffer) {
        try {
            if (zeroDigit == 0) {
                zeroDigit = ((DecimalFormat)(DecimalFormat)numberFormat).getDecimalFormatSymbols().getZeroDigit();
            }
            if (value >= 0) {
                if (value < 100 && minDigits >= 1 && minDigits <= 2) {
                    if (value < 10) {
                        if (minDigits == 2) {
                            buffer.append(zeroDigit);
                        }
                        buffer.append((char)(zeroDigit + value));
                    } else {
                        buffer.append((char)(zeroDigit + value / 10));
                        buffer.append((char)(zeroDigit + value % 10));
                    }
                    return;
                } else if (value >= 1000 && value < 10000) {
                    if (minDigits == 4) {
                        buffer.append((char)(zeroDigit + value / 1000));
                        value %= 1000;
                        buffer.append((char)(zeroDigit + value / 100));
                        value %= 100;
                        buffer.append((char)(zeroDigit + value / 10));
                        buffer.append((char)(zeroDigit + value % 10));
                        return;
                    }
                    if (minDigits == 2 && maxDigits == 2) {
                        zeroPaddingNumber(value % 100, 2, 2, buffer);
                        return;
                    }
                }
            }
        } catch (Exception e) {
        }
        numberFormat.setMinimumIntegerDigits(minDigits);
        numberFormat.setMaximumIntegerDigits(maxDigits);
        numberFormat.format((long)value, buffer, DontCareFieldPosition.INSTANCE);
    }
    
    public Date parse(String text, ParsePosition pos) {
        int start = pos.index;
        int oldStart = start;
        int textLength = text.length();
        boolean[] ambiguousYear = {false};
        calendar.clear();
        for (int i = 0; i < compiledPattern.length; ) {
            int tag = compiledPattern[i] >>> 8;
            int count = compiledPattern[i++] & 255;
            if (count == 255) {
                count = compiledPattern[i++] << 16;
                count |= compiledPattern[i++];
            }
            switch (tag) {
            case TAG_QUOTE_ASCII_CHAR: 
                if (start >= textLength || text.charAt(start) != (char)count) {
                    pos.index = oldStart;
                    pos.errorIndex = start;
                    return null;
                }
                start++;
                break;
            
            case TAG_QUOTE_CHARS: 
                while (count-- > 0) {
                    if (start >= textLength || text.charAt(start) != compiledPattern[i++]) {
                        pos.index = oldStart;
                        pos.errorIndex = start;
                        return null;
                    }
                    start++;
                }
                break;
            
            default: 
                boolean obeyCount = false;
                if (i < compiledPattern.length) {
                    int nextTag = compiledPattern[i] >>> 8;
                    if (!(nextTag == TAG_QUOTE_ASCII_CHAR || nextTag == TAG_QUOTE_CHARS)) {
                        obeyCount = true;
                    }
                }
                start = subParse(text, start, tag, count, obeyCount, ambiguousYear, pos);
                if (start < 0) {
                    pos.index = oldStart;
                    return null;
                }
            
            }
        }
        pos.index = start;
        Date parsedDate;
        try {
            if (ambiguousYear[0]) {
                Calendar savedCalendar = (Calendar)(Calendar)calendar.clone();
                parsedDate = calendar.getTime();
                if (parsedDate.before(defaultCenturyStart)) {
                    savedCalendar.set(Calendar.YEAR, defaultCenturyStartYear + 100);
                    parsedDate = savedCalendar.getTime();
                }
            } else parsedDate = calendar.getTime();
        } catch (IllegalArgumentException e) {
            pos.errorIndex = start;
            pos.index = oldStart;
            return null;
        }
        return parsedDate;
    }
    
    private int matchString(String text, int start, int field, String[] data) {
        int i = 0;
        int count = data.length;
        if (field == Calendar.DAY_OF_WEEK) i = 1;
        int bestMatchLength = 0;
        int bestMatch = -1;
        for (; i < count; ++i) {
            int length = data[i].length();
            if (length > bestMatchLength && text.regionMatches(true, start, data[i], 0, length)) {
                bestMatch = i;
                bestMatchLength = length;
            }
        }
        if (bestMatch >= 0) {
            calendar.set(field, bestMatch);
            return start + bestMatchLength;
        }
        return -start;
    }
    
    private int matchZoneString(String text, int start, int zoneIndex) {
        for (int j = 1; j <= 4; ++j) {
            String zoneName = formatData.zoneStrings[zoneIndex][j];
            if (text.regionMatches(true, start, zoneName, 0, zoneName.length())) {
                return j;
            }
        }
        return -1;
    }
    
    private boolean matchDSTString(String text, int start, int zoneIndex, int standardIndex) {
        int index = standardIndex + 2;
        String zoneName = formatData.zoneStrings[zoneIndex][index];
        if (text.regionMatches(true, start, zoneName, 0, zoneName.length())) {
            return true;
        }
        return false;
    }
    
    private int subParseZoneString(String text, int start) {
        boolean useSameName = false;
        TimeZone currentTimeZone = getTimeZone();
        int zoneIndex = formatData.getZoneIndex(currentTimeZone.getID());
        TimeZone tz = null;
        int j = 0;
        int i = 0;
        if ((zoneIndex != -1) && ((j = matchZoneString(text, start, zoneIndex)) > 0)) {
            if (j <= 2) {
                useSameName = matchDSTString(text, start, zoneIndex, j);
            }
            tz = TimeZone.getTimeZone(formatData.zoneStrings[zoneIndex][0]);
            i = zoneIndex;
        }
        if (tz == null) {
            zoneIndex = formatData.getZoneIndex(TimeZone.getDefault().getID());
            if ((zoneIndex != -1) && ((j = matchZoneString(text, start, zoneIndex)) > 0)) {
                if (j <= 2) {
                    useSameName = matchDSTString(text, start, zoneIndex, j);
                }
                tz = TimeZone.getTimeZone(formatData.zoneStrings[zoneIndex][0]);
                i = zoneIndex;
            }
        }
        if (tz == null) {
            for (i = 0; i < formatData.zoneStrings.length; i++) {
                if ((j = matchZoneString(text, start, i)) > 0) {
                    if (j <= 2) {
                        useSameName = matchDSTString(text, start, i, j);
                    }
                    tz = TimeZone.getTimeZone(formatData.zoneStrings[i][0]);
                    break;
                }
            }
        }
        if (tz != null) {
            if (!tz.equals(currentTimeZone)) {
                setTimeZone(tz);
            }
            if (!useSameName) {
                calendar.set(Calendar.ZONE_OFFSET, tz.getRawOffset());
                calendar.set(Calendar.DST_OFFSET, j >= 3 ? tz.getDSTSavings() : 0);
            }
            return (start + formatData.zoneStrings[i][j].length());
        }
        return 0;
    }
    
    private int subParse(String text, int start, int patternCharIndex, int count, boolean obeyCount, boolean[] ambiguousYear, ParsePosition origPos) {
        Number number = null;
        int value = 0;
        ParsePosition pos = new ParsePosition(0);
        pos.index = start;
        int field = PATTERN_INDEX_TO_CALENDAR_FIELD[patternCharIndex];
        for (; ; ) {
            if (pos.index >= text.length()) {
                origPos.errorIndex = start;
                return -1;
            }
            char c = text.charAt(pos.index);
            if (c != ' ' && c != '\t') break;
            ++pos.index;
        }
        if (patternCharIndex == 4 || patternCharIndex == 15 || (patternCharIndex == 2 && count <= 2) || patternCharIndex == 1) {
            if (obeyCount) {
                if ((start + count) > text.length()) {
                    origPos.errorIndex = start;
                    return -1;
                }
                number = numberFormat.parse(text.substring(0, start + count), pos);
            } else number = numberFormat.parse(text, pos);
            if (number == null) {
                origPos.errorIndex = pos.index;
                return -1;
            }
            value = number.intValue();
        }
        int index;
        switch (patternCharIndex) {
        case 0: 
            if ((index = matchString(text, start, Calendar.ERA, formatData.eras)) > 0) {
                return index;
            } else {
                origPos.errorIndex = pos.index;
                return -1;
            }
        
        case 1: 
            if (count <= 2 && (pos.index - start) == 2 && Character.isDigit(text.charAt(start)) && Character.isDigit(text.charAt(start + 1))) {
                int ambiguousTwoDigitYear = defaultCenturyStartYear % 100;
                ambiguousYear[0] = value == ambiguousTwoDigitYear;
                value += (defaultCenturyStartYear / 100) * 100 + (value < ambiguousTwoDigitYear ? 100 : 0);
            }
            calendar.set(Calendar.YEAR, value);
            return pos.index;
        
        case 2: 
            if (count <= 2) {
                calendar.set(Calendar.MONTH, value - 1);
                return pos.index;
            } else {
                int newStart = 0;
                if ((newStart = matchString(text, start, Calendar.MONTH, formatData.months)) > 0) return newStart; else if ((index = matchString(text, start, Calendar.MONTH, formatData.shortMonths)) > 0) {
                    return index;
                } else {
                    origPos.errorIndex = pos.index;
                    return -1;
                }
            }
        
        case 4: 
            if (value == calendar.getMaximum(Calendar.HOUR_OF_DAY) + 1) value = 0;
            calendar.set(Calendar.HOUR_OF_DAY, value);
            return pos.index;
        
        case 9: 
            {
                int newStart = 0;
                if ((newStart = matchString(text, start, Calendar.DAY_OF_WEEK, formatData.weekdays)) > 0) return newStart; else if ((index = matchString(text, start, Calendar.DAY_OF_WEEK, formatData.shortWeekdays)) > 0) {
                    return index;
                } else {
                    origPos.errorIndex = pos.index;
                    return -1;
                }
            }
        
        case 14: 
            if ((index = matchString(text, start, Calendar.AM_PM, formatData.ampms)) > 0) {
                return index;
            } else {
                origPos.errorIndex = pos.index;
                return -1;
            }
        
        case 15: 
            if (value == calendar.getLeastMaximum(Calendar.HOUR) + 1) value = 0;
            calendar.set(Calendar.HOUR, value);
            return pos.index;
        
        case 17: 
        
        case 18: 
            {
                int sign = 0;
                int offset;
                if ((text.length() - start) >= GMT.length() && text.regionMatches(true, start, GMT, 0, GMT.length())) {
                    int num;
                    calendar.set(Calendar.DST_OFFSET, 0);
                    pos.index = start + GMT.length();
                    try {
                        if (text.charAt(pos.index) == '+') {
                            sign = 1;
                        } else if (text.charAt(pos.index) == '-') {
                            sign = -1;
                        }
                    } catch (StringIndexOutOfBoundsException e) {
                    }
                    if (sign == 0) {
                        calendar.set(Calendar.ZONE_OFFSET, 0);
                        return pos.index;
                    }
                    try {
                        char c = text.charAt(++pos.index);
                        if (c < '0' || c > '9') {
                            origPos.errorIndex = pos.index;
                            return -1;
                        } else {
                            num = c - '0';
                        }
                        if (text.charAt(++pos.index) != ':') {
                            c = text.charAt(pos.index);
                            if (c < '0' || c > '9') {
                                origPos.errorIndex = pos.index;
                                return -1;
                            } else {
                                num *= 10;
                                num += c - '0';
                                pos.index++;
                            }
                        }
                        if (num > 23) {
                            origPos.errorIndex = pos.index - 1;
                            return -1;
                        }
                        if (text.charAt(pos.index) != ':') {
                            origPos.errorIndex = pos.index;
                            return -1;
                        }
                    } catch (StringIndexOutOfBoundsException e) {
                        origPos.errorIndex = pos.index;
                        return -1;
                    }
                    offset = num * 60;
                    try {
                        char c = text.charAt(++pos.index);
                        if (c < '0' || c > '9') {
                            origPos.errorIndex = pos.index;
                            return -1;
                        } else {
                            num = c - '0';
                            c = text.charAt(++pos.index);
                            if (c < '0' || c > '9') {
                                origPos.errorIndex = pos.index;
                                return -1;
                            } else {
                                num *= 10;
                                num += c - '0';
                            }
                        }
                        if (num > 59) {
                            origPos.errorIndex = pos.index;
                            return -1;
                        }
                    } catch (StringIndexOutOfBoundsException e) {
                        origPos.errorIndex = pos.index;
                        return -1;
                    }
                    offset += num;
                } else {
                    int i = subParseZoneString(text, pos.index);
                    if (i != 0) {
                        return i;
                    }
                    try {
                        if (text.charAt(pos.index) == '+') {
                            sign = 1;
                        } else if (text.charAt(pos.index) == '-') {
                            sign = -1;
                        }
                        if (sign == 0) {
                            origPos.errorIndex = pos.index;
                            return -1;
                        }
                        int hours = 0;
                        char c = text.charAt(++pos.index);
                        if (c < '0' || c > '9') {
                            origPos.errorIndex = pos.index;
                            return -1;
                        } else {
                            hours = c - '0';
                            c = text.charAt(++pos.index);
                            if (c < '0' || c > '9') {
                                origPos.errorIndex = pos.index;
                                return -1;
                            } else {
                                hours *= 10;
                                hours += c - '0';
                            }
                        }
                        if (hours > 23) {
                            origPos.errorIndex = pos.index;
                            return -1;
                        }
                        int minutes = 0;
                        c = text.charAt(++pos.index);
                        if (c < '0' || c > '9') {
                            origPos.errorIndex = pos.index;
                            return -1;
                        } else {
                            minutes = c - '0';
                            c = text.charAt(++pos.index);
                            if (c < '0' || c > '9') {
                                origPos.errorIndex = pos.index;
                                return -1;
                            } else {
                                minutes *= 10;
                                minutes += c - '0';
                            }
                        }
                        if (minutes > 59) {
                            origPos.errorIndex = pos.index;
                            return -1;
                        }
                        offset = hours * 60 + minutes;
                    } catch (StringIndexOutOfBoundsException e) {
                        origPos.errorIndex = pos.index;
                        return -1;
                    }
                }
                if (sign != 0) {
                    offset *= millisPerMinute * sign;
                    calendar.set(Calendar.ZONE_OFFSET, offset);
                    calendar.set(Calendar.DST_OFFSET, 0);
                    return ++pos.index;
                }
            }
            origPos.errorIndex = pos.index;
            return -1;
        
        default: 
            if (obeyCount) {
                if ((start + count) > text.length()) {
                    origPos.errorIndex = pos.index;
                    return -1;
                }
                number = numberFormat.parse(text.substring(0, start + count), pos);
            } else number = numberFormat.parse(text, pos);
            if (number != null) {
                calendar.set(field, number.intValue());
                return pos.index;
            }
            origPos.errorIndex = pos.index;
            return -1;
        
        }
    }
    
    private String translatePattern(String pattern, String from, String to) {
        StringBuilder result = new StringBuilder();
        boolean inQuote = false;
        for (int i = 0; i < pattern.length(); ++i) {
            char c = pattern.charAt(i);
            if (inQuote) {
                if (c == '\'') inQuote = false;
            } else {
                if (c == '\'') inQuote = true; else if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) {
                    int ci = from.indexOf(c);
                    if (ci == -1) throw new IllegalArgumentException("Illegal pattern " + " character \'" + c + "\'");
                    c = to.charAt(ci);
                }
            }
            result.append(c);
        }
        if (inQuote) throw new IllegalArgumentException("Unfinished quote in pattern");
        return result.toString();
    }
    
    public String toPattern() {
        return pattern;
    }
    
    public String toLocalizedPattern() {
        return translatePattern(pattern, formatData.patternChars, formatData.localPatternChars);
    }
    
    public void applyPattern(String pattern) {
        compiledPattern = compile(pattern);
        this.pattern = pattern;
    }
    
    public void applyLocalizedPattern(String pattern) {
        String p = translatePattern(pattern, formatData.localPatternChars, formatData.patternChars);
        compiledPattern = compile(p);
        this.pattern = p;
    }
    
    public DateFormatSymbols getDateFormatSymbols() {
        return (DateFormatSymbols)(DateFormatSymbols)formatData.clone();
    }
    
    public void setDateFormatSymbols(DateFormatSymbols newFormatSymbols) {
        this.formatData = (DateFormatSymbols)(DateFormatSymbols)newFormatSymbols.clone();
    }
    
    public Object clone() {
        SimpleDateFormat other = (SimpleDateFormat)(SimpleDateFormat)super.clone();
        other.formatData = (DateFormatSymbols)(DateFormatSymbols)formatData.clone();
        return other;
    }
    
    public int hashCode() {
        return pattern.hashCode();
    }
    
    public boolean equals(Object obj) {
        if (!super.equals(obj)) return false;
        SimpleDateFormat that = (SimpleDateFormat)(SimpleDateFormat)obj;
        return (pattern.equals(that.pattern) && formatData.equals(that.formatData));
    }
    
    private void readObject(ObjectInputStream stream) throws IOException, ClassNotFoundException {
        stream.defaultReadObject();
        try {
            compiledPattern = compile(pattern);
        } catch (Exception e) {
            throw new InvalidObjectException("invalid pattern");
        }
        if (serialVersionOnStream < 1) {
            initializeDefaultCentury();
        } else {
            parseAmbiguousDatesAsAfter(defaultCenturyStart);
        }
        serialVersionOnStream = currentSerialVersion;
        TimeZone tz = getTimeZone();
        if (tz instanceof SimpleTimeZone) {
            String id = tz.getID();
            TimeZone zi = TimeZone.getTimeZone(id);
            if (zi != null && zi.hasSameRules(tz) && zi.getID().equals(id)) {
                setTimeZone(zi);
            }
        }
    }
}
