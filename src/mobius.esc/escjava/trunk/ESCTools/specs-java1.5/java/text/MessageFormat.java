package java.text;

import java.io.InvalidObjectException;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.Locale;
import sun.text.Utility;

public class MessageFormat extends Format {
    private static final long serialVersionUID = 6479157306784022952L;
    
    public MessageFormat(String pattern) {
        
        this.locale = Locale.getDefault();
        applyPattern(pattern);
    }
    
    public MessageFormat(String pattern, Locale locale) {
        
        this.locale = locale;
        applyPattern(pattern);
    }
    
    public void setLocale(Locale locale) {
        this.locale = locale;
    }
    
    public Locale getLocale() {
        return locale;
    }
    
    public void applyPattern(String pattern) {
        StringBuffer[] segments = new StringBuffer[4];
        for (int i = 0; i < segments.length; ++i) {
            segments[i] = new StringBuffer();
        }
        int part = 0;
        int formatNumber = 0;
        boolean inQuote = false;
        int braceStack = 0;
        maxOffset = -1;
        for (int i = 0; i < pattern.length(); ++i) {
            char ch = pattern.charAt(i);
            if (part == 0) {
                if (ch == '\'') {
                    if (i + 1 < pattern.length() && pattern.charAt(i + 1) == '\'') {
                        segments[part].append(ch);
                        ++i;
                    } else {
                        inQuote = !inQuote;
                    }
                } else if (ch == '{' && !inQuote) {
                    part = 1;
                } else {
                    segments[part].append(ch);
                }
            } else if (inQuote) {
                segments[part].append(ch);
                if (ch == '\'') {
                    inQuote = false;
                }
            } else {
                switch (ch) {
                case ',': 
                    if (part < 3) part += 1; else segments[part].append(ch);
                    break;
                
                case '{': 
                    ++braceStack;
                    segments[part].append(ch);
                    break;
                
                case '}': 
                    if (braceStack == 0) {
                        part = 0;
                        makeFormat(i, formatNumber, segments);
                        formatNumber++;
                    } else {
                        --braceStack;
                        segments[part].append(ch);
                    }
                    break;
                
                case '\'': 
                    inQuote = true;
                
                default: 
                    segments[part].append(ch);
                    break;
                
                }
            }
        }
        if (braceStack == 0 && part != 0) {
            maxOffset = -1;
            throw new IllegalArgumentException("Unmatched braces in the pattern.");
        }
        this.pattern = segments[0].toString();
    }
    
    public String toPattern() {
        int lastOffset = 0;
        StringBuffer result = new StringBuffer();
        for (int i = 0; i <= maxOffset; ++i) {
            copyAndFixQuotes(pattern, lastOffset, offsets[i], result);
            lastOffset = offsets[i];
            result.append('{');
            result.append(argumentNumbers[i]);
            if (formats[i] == null) {
            } else if (formats[i] instanceof DecimalFormat) {
                if (formats[i].equals(NumberFormat.getInstance(locale))) {
                    result.append(",number");
                } else if (formats[i].equals(NumberFormat.getCurrencyInstance(locale))) {
                    result.append(",number,currency");
                } else if (formats[i].equals(NumberFormat.getPercentInstance(locale))) {
                    result.append(",number,percent");
                } else if (formats[i].equals(NumberFormat.getIntegerInstance(locale))) {
                    result.append(",number,integer");
                } else {
                    result.append(",number," + ((DecimalFormat)(DecimalFormat)formats[i]).toPattern());
                }
            } else if (formats[i] instanceof SimpleDateFormat) {
                if (formats[i].equals(DateFormat.getDateInstance(DateFormat.DEFAULT, locale))) {
                    result.append(",date");
                } else if (formats[i].equals(DateFormat.getDateInstance(DateFormat.SHORT, locale))) {
                    result.append(",date,short");
                } else if (formats[i].equals(DateFormat.getDateInstance(DateFormat.DEFAULT, locale))) {
                    result.append(",date,medium");
                } else if (formats[i].equals(DateFormat.getDateInstance(DateFormat.LONG, locale))) {
                    result.append(",date,long");
                } else if (formats[i].equals(DateFormat.getDateInstance(DateFormat.FULL, locale))) {
                    result.append(",date,full");
                } else if (formats[i].equals(DateFormat.getTimeInstance(DateFormat.DEFAULT, locale))) {
                    result.append(",time");
                } else if (formats[i].equals(DateFormat.getTimeInstance(DateFormat.SHORT, locale))) {
                    result.append(",time,short");
                } else if (formats[i].equals(DateFormat.getTimeInstance(DateFormat.DEFAULT, locale))) {
                    result.append(",time,medium");
                } else if (formats[i].equals(DateFormat.getTimeInstance(DateFormat.LONG, locale))) {
                    result.append(",time,long");
                } else if (formats[i].equals(DateFormat.getTimeInstance(DateFormat.FULL, locale))) {
                    result.append(",time,full");
                } else {
                    result.append(",date," + ((SimpleDateFormat)(SimpleDateFormat)formats[i]).toPattern());
                }
            } else if (formats[i] instanceof ChoiceFormat) {
                result.append(",choice," + ((ChoiceFormat)(ChoiceFormat)formats[i]).toPattern());
            } else {
            }
            result.append('}');
        }
        copyAndFixQuotes(pattern, lastOffset, pattern.length(), result);
        return result.toString();
    }
    
    public void setFormatsByArgumentIndex(Format[] newFormats) {
        for (int i = 0; i <= maxOffset; i++) {
            int j = argumentNumbers[i];
            if (j < newFormats.length) {
                formats[i] = newFormats[j];
            }
        }
    }
    
    public void setFormats(Format[] newFormats) {
        int runsToCopy = newFormats.length;
        if (runsToCopy > maxOffset + 1) {
            runsToCopy = maxOffset + 1;
        }
        for (int i = 0; i < runsToCopy; i++) {
            formats[i] = newFormats[i];
        }
    }
    
    public void setFormatByArgumentIndex(int argumentIndex, Format newFormat) {
        for (int j = 0; j <= maxOffset; j++) {
            if (argumentNumbers[j] == argumentIndex) {
                formats[j] = newFormat;
            }
        }
    }
    
    public void setFormat(int formatElementIndex, Format newFormat) {
        formats[formatElementIndex] = newFormat;
    }
    
    public Format[] getFormatsByArgumentIndex() {
        int maximumArgumentNumber = -1;
        for (int i = 0; i <= maxOffset; i++) {
            if (argumentNumbers[i] > maximumArgumentNumber) {
                maximumArgumentNumber = argumentNumbers[i];
            }
        }
        Format[] resultArray = new Format[maximumArgumentNumber + 1];
        for (int i = 0; i <= maxOffset; i++) {
            resultArray[argumentNumbers[i]] = formats[i];
        }
        return resultArray;
    }
    
    public Format[] getFormats() {
        Format[] resultArray = new Format[maxOffset + 1];
        System.arraycopy(formats, 0, resultArray, 0, maxOffset + 1);
        return resultArray;
    }
    
    public final StringBuffer format(Object[] arguments, StringBuffer result, FieldPosition pos) {
        return subformat(arguments, result, pos, null);
    }
    
    public static String format(String pattern, Object[] arguments) {
        MessageFormat temp = new MessageFormat(pattern);
        return temp.format(arguments);
    }
    
    public final StringBuffer format(Object arguments, StringBuffer result, FieldPosition pos) {
        return subformat((Object[])(Object[])arguments, result, pos, null);
    }
    
    public AttributedCharacterIterator formatToCharacterIterator(Object arguments) {
        StringBuffer result = new StringBuffer();
        ArrayList iterators = new ArrayList();
        if (arguments == null) {
            throw new NullPointerException("formatToCharacterIterator must be passed non-null object");
        }
        subformat((Object[])(Object[])arguments, result, null, iterators);
        if (iterators.size() == 0) {
            return createAttributedCharacterIterator("");
        }
        return createAttributedCharacterIterator((AttributedCharacterIterator[])(AttributedCharacterIterator[])iterators.toArray(new AttributedCharacterIterator[iterators.size()]));
    }
    
    public Object[] parse(String source, ParsePosition pos) {
        if (source == null) {
            Object[] empty = {};
            return empty;
        }
        int maximumArgumentNumber = -1;
        for (int i = 0; i <= maxOffset; i++) {
            if (argumentNumbers[i] > maximumArgumentNumber) {
                maximumArgumentNumber = argumentNumbers[i];
            }
        }
        Object[] resultArray = new Object[maximumArgumentNumber + 1];
        int patternOffset = 0;
        int sourceOffset = pos.index;
        ParsePosition tempStatus = new ParsePosition(0);
        for (int i = 0; i <= maxOffset; ++i) {
            int len = offsets[i] - patternOffset;
            if (len == 0 || pattern.regionMatches(patternOffset, source, sourceOffset, len)) {
                sourceOffset += len;
                patternOffset += len;
            } else {
                pos.errorIndex = sourceOffset;
                return null;
            }
            if (formats[i] == null) {
                int tempLength = (i != maxOffset) ? offsets[i + 1] : pattern.length();
                int next;
                if (patternOffset >= tempLength) {
                    next = source.length();
                } else {
                    next = source.indexOf(pattern.substring(patternOffset, tempLength), sourceOffset);
                }
                if (next < 0) {
                    pos.errorIndex = sourceOffset;
                    return null;
                } else {
                    String strValue = source.substring(sourceOffset, next);
                    if (!strValue.equals("{" + argumentNumbers[i] + "}")) resultArray[argumentNumbers[i]] = source.substring(sourceOffset, next);
                    sourceOffset = next;
                }
            } else {
                tempStatus.index = sourceOffset;
                resultArray[argumentNumbers[i]] = formats[i].parseObject(source, tempStatus);
                if (tempStatus.index == sourceOffset) {
                    pos.errorIndex = sourceOffset;
                    return null;
                }
                sourceOffset = tempStatus.index;
            }
        }
        int len = pattern.length() - patternOffset;
        if (len == 0 || pattern.regionMatches(patternOffset, source, sourceOffset, len)) {
            pos.index = sourceOffset + len;
        } else {
            pos.errorIndex = sourceOffset;
            return null;
        }
        return resultArray;
    }
    
    public Object[] parse(String source) throws ParseException {
        ParsePosition pos = new ParsePosition(0);
        Object[] result = parse(source, pos);
        if (pos.index == 0) throw new ParseException("MessageFormat parse error!", pos.errorIndex);
        return result;
    }
    
    public Object parseObject(String source, ParsePosition pos) {
        return parse(source, pos);
    }
    
    public Object clone() {
        MessageFormat other = (MessageFormat)(MessageFormat)super.clone();
        other.formats = (Format[])(Format[])formats.clone();
        for (int i = 0; i < formats.length; ++i) {
            if (formats[i] != null) other.formats[i] = (Format)(Format)formats[i].clone();
        }
        other.offsets = (int[])(int[])offsets.clone();
        other.argumentNumbers = (int[])(int[])argumentNumbers.clone();
        return other;
    }
    
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        MessageFormat other = (MessageFormat)(MessageFormat)obj;
        return (maxOffset == other.maxOffset && pattern.equals(other.pattern) && Utility.objectEquals(locale, other.locale) && Utility.arrayEquals(offsets, other.offsets) && Utility.arrayEquals(argumentNumbers, other.argumentNumbers) && Utility.arrayEquals(formats, other.formats));
    }
    
    public int hashCode() {
        return pattern.hashCode();
    }
    {
    }
    private Locale locale;
    private String pattern = "";
    private static final int INITIAL_FORMATS = 10;
    private Format[] formats = new Format[INITIAL_FORMATS];
    private int[] offsets = new int[INITIAL_FORMATS];
    private int[] argumentNumbers = new int[INITIAL_FORMATS];
    private int maxOffset = -1;
    
    private StringBuffer subformat(Object[] arguments, StringBuffer result, FieldPosition fp, List characterIterators) {
        int lastOffset = 0;
        int last = result.length();
        for (int i = 0; i <= maxOffset; ++i) {
            result.append(pattern.substring(lastOffset, offsets[i]));
            lastOffset = offsets[i];
            int argumentNumber = argumentNumbers[i];
            if (arguments == null || argumentNumber >= arguments.length) {
                result.append("{" + argumentNumber + "}");
                continue;
            }
            {
                Object obj = arguments[argumentNumber];
                String arg = null;
                Format subFormatter = null;
                if (obj == null) {
                    arg = "null";
                } else if (formats[i] != null) {
                    subFormatter = formats[i];
                    if (subFormatter instanceof ChoiceFormat) {
                        arg = formats[i].format(obj);
                        if (arg.indexOf('{') >= 0) {
                            subFormatter = new MessageFormat(arg, locale);
                            obj = arguments;
                            arg = null;
                        }
                    }
                } else if (obj instanceof Number) {
                    subFormatter = NumberFormat.getInstance(locale);
                } else if (obj instanceof Date) {
                    subFormatter = DateFormat.getDateTimeInstance(DateFormat.SHORT, DateFormat.SHORT, locale);
                } else if (obj instanceof String) {
                    arg = (String)(String)obj;
                } else {
                    arg = obj.toString();
                    if (arg == null) arg = "null";
                }
                if (characterIterators != null) {
                    if (last != result.length()) {
                        characterIterators.add(createAttributedCharacterIterator(result.substring(last)));
                        last = result.length();
                    }
                    if (subFormatter != null) {
                        AttributedCharacterIterator subIterator = subFormatter.formatToCharacterIterator(obj);
                        append(result, subIterator);
                        if (last != result.length()) {
                            characterIterators.add(createAttributedCharacterIterator(subIterator, MessageFormat$Field.ARGUMENT, new Integer(argumentNumber)));
                            last = result.length();
                        }
                        arg = null;
                    }
                    if (arg != null && arg.length() > 0) {
                        result.append(arg);
                        characterIterators.add(createAttributedCharacterIterator(arg, MessageFormat$Field.ARGUMENT, new Integer(argumentNumber)));
                        last = result.length();
                    }
                } else {
                    if (subFormatter != null) {
                        arg = subFormatter.format(obj);
                    }
                    last = result.length();
                    result.append(arg);
                    if (i == 0 && fp != null && MessageFormat$Field.ARGUMENT.equals(fp.getFieldAttribute())) {
                        fp.setBeginIndex(last);
                        fp.setEndIndex(result.length());
                    }
                    last = result.length();
                }
            }
        }
        result.append(pattern.substring(lastOffset, pattern.length()));
        if (characterIterators != null && last != result.length()) {
            characterIterators.add(createAttributedCharacterIterator(result.substring(last)));
        }
        return result;
    }
    
    private void append(StringBuffer result, CharacterIterator iterator) {
        if (iterator.first() != CharacterIterator.DONE) {
            char aChar;
            result.append(iterator.first());
            while ((aChar = iterator.next()) != CharacterIterator.DONE) {
                result.append(aChar);
            }
        }
    }
    private static final String[] typeList = {"", "", "number", "", "date", "", "time", "", "choice"};
    private static final String[] modifierList = {"", "", "currency", "", "percent", "", "integer"};
    private static final String[] dateModifierList = {"", "", "short", "", "medium", "", "long", "", "full"};
    
    private void makeFormat(int position, int offsetNumber, StringBuffer[] segments) {
        int argumentNumber;
        try {
            argumentNumber = Integer.parseInt(segments[1].toString());
        } catch (NumberFormatException e) {
            throw new IllegalArgumentException("can\'t parse argument number " + segments[1]);
        }
        if (argumentNumber < 0) {
            throw new IllegalArgumentException("negative argument number " + argumentNumber);
        }
        if (offsetNumber >= formats.length) {
            int newLength = formats.length * 2;
            Format[] newFormats = new Format[newLength];
            int[] newOffsets = new int[newLength];
            int[] newArgumentNumbers = new int[newLength];
            System.arraycopy(formats, 0, newFormats, 0, maxOffset + 1);
            System.arraycopy(offsets, 0, newOffsets, 0, maxOffset + 1);
            System.arraycopy(argumentNumbers, 0, newArgumentNumbers, 0, maxOffset + 1);
            formats = newFormats;
            offsets = newOffsets;
            argumentNumbers = newArgumentNumbers;
        }
        int oldMaxOffset = maxOffset;
        maxOffset = offsetNumber;
        offsets[offsetNumber] = segments[0].length();
        argumentNumbers[offsetNumber] = argumentNumber;
        Format newFormat = null;
        switch (findKeyword(segments[2].toString(), typeList)) {
        case 0: 
            break;
        
        case 1: 
        
        case 2: 
            switch (findKeyword(segments[3].toString(), modifierList)) {
            case 0: 
                newFormat = NumberFormat.getInstance(locale);
                break;
            
            case 1: 
            
            case 2: 
                newFormat = NumberFormat.getCurrencyInstance(locale);
                break;
            
            case 3: 
            
            case 4: 
                newFormat = NumberFormat.getPercentInstance(locale);
                break;
            
            case 5: 
            
            case 6: 
                newFormat = NumberFormat.getIntegerInstance(locale);
                break;
            
            default: 
                newFormat = new DecimalFormat(segments[3].toString(), new DecimalFormatSymbols(locale));
                break;
            
            }
            break;
        
        case 3: 
        
        case 4: 
            switch (findKeyword(segments[3].toString(), dateModifierList)) {
            case 0: 
                newFormat = DateFormat.getDateInstance(DateFormat.DEFAULT, locale);
                break;
            
            case 1: 
            
            case 2: 
                newFormat = DateFormat.getDateInstance(DateFormat.SHORT, locale);
                break;
            
            case 3: 
            
            case 4: 
                newFormat = DateFormat.getDateInstance(DateFormat.DEFAULT, locale);
                break;
            
            case 5: 
            
            case 6: 
                newFormat = DateFormat.getDateInstance(DateFormat.LONG, locale);
                break;
            
            case 7: 
            
            case 8: 
                newFormat = DateFormat.getDateInstance(DateFormat.FULL, locale);
                break;
            
            default: 
                newFormat = new SimpleDateFormat(segments[3].toString(), locale);
                break;
            
            }
            break;
        
        case 5: 
        
        case 6: 
            switch (findKeyword(segments[3].toString(), dateModifierList)) {
            case 0: 
                newFormat = DateFormat.getTimeInstance(DateFormat.DEFAULT, locale);
                break;
            
            case 1: 
            
            case 2: 
                newFormat = DateFormat.getTimeInstance(DateFormat.SHORT, locale);
                break;
            
            case 3: 
            
            case 4: 
                newFormat = DateFormat.getTimeInstance(DateFormat.DEFAULT, locale);
                break;
            
            case 5: 
            
            case 6: 
                newFormat = DateFormat.getTimeInstance(DateFormat.LONG, locale);
                break;
            
            case 7: 
            
            case 8: 
                newFormat = DateFormat.getTimeInstance(DateFormat.FULL, locale);
                break;
            
            default: 
                newFormat = new SimpleDateFormat(segments[3].toString(), locale);
                break;
            
            }
            break;
        
        case 7: 
        
        case 8: 
            try {
                newFormat = new ChoiceFormat(segments[3].toString());
            } catch (Exception e) {
                maxOffset = oldMaxOffset;
                throw new IllegalArgumentException("Choice Pattern incorrect");
            }
            break;
        
        default: 
            maxOffset = oldMaxOffset;
            throw new IllegalArgumentException("unknown format type at ");
        
        }
        formats[offsetNumber] = newFormat;
        segments[1].setLength(0);
        segments[2].setLength(0);
        segments[3].setLength(0);
    }
    
    private static final int findKeyword(String s, String[] list) {
        s = s.trim().toLowerCase();
        for (int i = 0; i < list.length; ++i) {
            if (s.equals(list[i])) return i;
        }
        return -1;
    }
    
    private static final void copyAndFixQuotes(String source, int start, int end, StringBuffer target) {
        for (int i = start; i < end; ++i) {
            char ch = source.charAt(i);
            if (ch == '{') {
                target.append("\'{\'");
            } else if (ch == '}') {
                target.append("\'}\'");
            } else if (ch == '\'') {
                target.append("\'\'");
            } else {
                target.append(ch);
            }
        }
    }
    
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        boolean isValid = maxOffset >= -1 && formats.length > maxOffset && offsets.length > maxOffset && argumentNumbers.length > maxOffset;
        if (isValid) {
            int lastOffset = pattern.length() + 1;
            for (int i = maxOffset; i >= 0; --i) {
                if ((offsets[i] < 0) || (offsets[i] > lastOffset)) {
                    isValid = false;
                    break;
                } else {
                    lastOffset = offsets[i];
                }
            }
        }
        if (!isValid) {
            throw new InvalidObjectException("Could not reconstruct MessageFormat from corrupt stream.");
        }
    }
}
