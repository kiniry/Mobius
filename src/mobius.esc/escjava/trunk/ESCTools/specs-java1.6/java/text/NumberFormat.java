package java.text;

import java.io.InvalidObjectException;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.math.BigInteger;
import java.util.Currency;
import java.util.Hashtable;
import java.util.Locale;
import java.util.ResourceBundle;
import sun.text.resources.LocaleData;

public abstract class NumberFormat extends Format {
    
    public NumberFormat() {
        
    }
    public static final int INTEGER_FIELD = 0;
    public static final int FRACTION_FIELD = 1;
    
    public StringBuffer format(Object number, StringBuffer toAppendTo, FieldPosition pos) {
        if (number instanceof Long || number instanceof Integer || number instanceof Short || number instanceof Byte || (number instanceof BigInteger && ((BigInteger)(BigInteger)number).bitLength() < 64)) {
            return format(((Number)(Number)number).longValue(), toAppendTo, pos);
        } else if (number instanceof Number) {
            return format(((Number)(Number)number).doubleValue(), toAppendTo, pos);
        } else {
            throw new IllegalArgumentException("Cannot format given Object as a Number");
        }
    }
    
    public final Object parseObject(String source, ParsePosition pos) {
        return parse(source, pos);
    }
    
    public final String format(double number) {
        return format(number, new StringBuffer(), DontCareFieldPosition.INSTANCE).toString();
    }
    
    public final String format(long number) {
        return format(number, new StringBuffer(), DontCareFieldPosition.INSTANCE).toString();
    }
    
    public abstract StringBuffer format(double number, StringBuffer toAppendTo, FieldPosition pos);
    
    public abstract StringBuffer format(long number, StringBuffer toAppendTo, FieldPosition pos);
    
    public abstract Number parse(String source, ParsePosition parsePosition);
    
    public Number parse(String source) throws ParseException {
        ParsePosition parsePosition = new ParsePosition(0);
        Number result = parse(source, parsePosition);
        if (parsePosition.index == 0) {
            throw new ParseException("Unparseable number: \"" + source + "\"", parsePosition.errorIndex);
        }
        return result;
    }
    
    public boolean isParseIntegerOnly() {
        return parseIntegerOnly;
    }
    
    public void setParseIntegerOnly(boolean value) {
        parseIntegerOnly = value;
    }
    
    public static final NumberFormat getInstance() {
        return getInstance(Locale.getDefault(), NUMBERSTYLE);
    }
    
    public static NumberFormat getInstance(Locale inLocale) {
        return getInstance(inLocale, NUMBERSTYLE);
    }
    
    public static final NumberFormat getNumberInstance() {
        return getInstance(Locale.getDefault(), NUMBERSTYLE);
    }
    
    public static NumberFormat getNumberInstance(Locale inLocale) {
        return getInstance(inLocale, NUMBERSTYLE);
    }
    
    public static final NumberFormat getIntegerInstance() {
        return getInstance(Locale.getDefault(), INTEGERSTYLE);
    }
    
    public static NumberFormat getIntegerInstance(Locale inLocale) {
        return getInstance(inLocale, INTEGERSTYLE);
    }
    
    public static final NumberFormat getCurrencyInstance() {
        return getInstance(Locale.getDefault(), CURRENCYSTYLE);
    }
    
    public static NumberFormat getCurrencyInstance(Locale inLocale) {
        return getInstance(inLocale, CURRENCYSTYLE);
    }
    
    public static final NumberFormat getPercentInstance() {
        return getInstance(Locale.getDefault(), PERCENTSTYLE);
    }
    
    public static NumberFormat getPercentInstance(Locale inLocale) {
        return getInstance(inLocale, PERCENTSTYLE);
    }
    
    static final NumberFormat getScientificInstance() {
        return getInstance(Locale.getDefault(), SCIENTIFICSTYLE);
    }
    
    static NumberFormat getScientificInstance(Locale inLocale) {
        return getInstance(inLocale, SCIENTIFICSTYLE);
    }
    
    public static Locale[] getAvailableLocales() {
        return LocaleData.getAvailableLocales("NumberPatterns");
    }
    
    public int hashCode() {
        return maximumIntegerDigits * 37 + maxFractionDigits;
    }
    
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (this == obj) {
            return true;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        NumberFormat other = (NumberFormat)(NumberFormat)obj;
        return (maximumIntegerDigits == other.maximumIntegerDigits && minimumIntegerDigits == other.minimumIntegerDigits && maximumFractionDigits == other.maximumFractionDigits && minimumFractionDigits == other.minimumFractionDigits && groupingUsed == other.groupingUsed && parseIntegerOnly == other.parseIntegerOnly);
    }
    
    public Object clone() {
        NumberFormat other = (NumberFormat)(NumberFormat)super.clone();
        return other;
    }
    
    public boolean isGroupingUsed() {
        return groupingUsed;
    }
    
    public void setGroupingUsed(boolean newValue) {
        groupingUsed = newValue;
    }
    
    public int getMaximumIntegerDigits() {
        return maximumIntegerDigits;
    }
    
    public void setMaximumIntegerDigits(int newValue) {
        maximumIntegerDigits = Math.max(0, newValue);
        if (minimumIntegerDigits > maximumIntegerDigits) {
            minimumIntegerDigits = maximumIntegerDigits;
        }
    }
    
    public int getMinimumIntegerDigits() {
        return minimumIntegerDigits;
    }
    
    public void setMinimumIntegerDigits(int newValue) {
        minimumIntegerDigits = Math.max(0, newValue);
        if (minimumIntegerDigits > maximumIntegerDigits) {
            maximumIntegerDigits = minimumIntegerDigits;
        }
    }
    
    public int getMaximumFractionDigits() {
        return maximumFractionDigits;
    }
    
    public void setMaximumFractionDigits(int newValue) {
        maximumFractionDigits = Math.max(0, newValue);
        if (maximumFractionDigits < minimumFractionDigits) {
            minimumFractionDigits = maximumFractionDigits;
        }
    }
    
    public int getMinimumFractionDigits() {
        return minimumFractionDigits;
    }
    
    public void setMinimumFractionDigits(int newValue) {
        minimumFractionDigits = Math.max(0, newValue);
        if (maximumFractionDigits < minimumFractionDigits) {
            maximumFractionDigits = minimumFractionDigits;
        }
    }
    
    public Currency getCurrency() {
        throw new UnsupportedOperationException();
    }
    
    public void setCurrency(Currency currency) {
        throw new UnsupportedOperationException();
    }
    
    private static NumberFormat getInstance(Locale desiredLocale, int choice) {
        String[] numberPatterns = (String[])(String[])cachedLocaleData.get(desiredLocale);
        if (numberPatterns == null) {
            ResourceBundle resource = LocaleData.getLocaleElements(desiredLocale);
            numberPatterns = resource.getStringArray("NumberPatterns");
            cachedLocaleData.put(desiredLocale, numberPatterns);
        }
        DecimalFormatSymbols symbols = new DecimalFormatSymbols(desiredLocale);
        int entry = (choice == INTEGERSTYLE) ? NUMBERSTYLE : choice;
        DecimalFormat format = new DecimalFormat(numberPatterns[entry], symbols);
        if (choice == INTEGERSTYLE) {
            format.setMaximumFractionDigits(0);
            format.setDecimalSeparatorAlwaysShown(false);
            format.setParseIntegerOnly(true);
        } else if (choice == CURRENCYSTYLE) {
            format.adjustForCurrencyDefaultFractionDigits();
        }
        return format;
    }
    
    private void readObject(ObjectInputStream stream) throws IOException, ClassNotFoundException {
        stream.defaultReadObject();
        if (serialVersionOnStream < 1) {
            maximumIntegerDigits = maxIntegerDigits;
            minimumIntegerDigits = minIntegerDigits;
            maximumFractionDigits = maxFractionDigits;
            minimumFractionDigits = minFractionDigits;
        }
        if (minimumIntegerDigits > maximumIntegerDigits || minimumFractionDigits > maximumFractionDigits || minimumIntegerDigits < 0 || minimumFractionDigits < 0) {
            throw new InvalidObjectException("Digit count range invalid");
        }
        serialVersionOnStream = currentSerialVersion;
    }
    
    private void writeObject(ObjectOutputStream stream) throws IOException {
        maxIntegerDigits = (maximumIntegerDigits > Byte.MAX_VALUE) ? Byte.MAX_VALUE : (byte)maximumIntegerDigits;
        minIntegerDigits = (minimumIntegerDigits > Byte.MAX_VALUE) ? Byte.MAX_VALUE : (byte)minimumIntegerDigits;
        maxFractionDigits = (maximumFractionDigits > Byte.MAX_VALUE) ? Byte.MAX_VALUE : (byte)maximumFractionDigits;
        minFractionDigits = (minimumFractionDigits > Byte.MAX_VALUE) ? Byte.MAX_VALUE : (byte)minimumFractionDigits;
        stream.defaultWriteObject();
    }
    private static final Hashtable cachedLocaleData = new Hashtable(3);
    private static final int NUMBERSTYLE = 0;
    private static final int CURRENCYSTYLE = 1;
    private static final int PERCENTSTYLE = 2;
    private static final int SCIENTIFICSTYLE = 3;
    private static final int INTEGERSTYLE = 4;
    private boolean groupingUsed = true;
    private byte maxIntegerDigits = 40;
    private byte minIntegerDigits = 1;
    private byte maxFractionDigits = 3;
    private byte minFractionDigits = 0;
    private boolean parseIntegerOnly = false;
    private int maximumIntegerDigits = 40;
    private int minimumIntegerDigits = 1;
    private int maximumFractionDigits = 3;
    private int minimumFractionDigits = 0;
    static final int currentSerialVersion = 1;
    private int serialVersionOnStream = currentSerialVersion;
    static final long serialVersionUID = -2308460125733713944L;
    {
    }
}
