package java.text;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.Serializable;
import java.util.Currency;
import java.util.Hashtable;
import java.util.Locale;
import java.util.ResourceBundle;
import sun.text.resources.LocaleData;

public final class DecimalFormatSymbols implements Cloneable, Serializable {
    
    public DecimalFormatSymbols() {
        
        initialize(Locale.getDefault());
    }
    
    public DecimalFormatSymbols(Locale locale) {
        
        initialize(locale);
    }
    
    public char getZeroDigit() {
        return zeroDigit;
    }
    
    public void setZeroDigit(char zeroDigit) {
        this.zeroDigit = zeroDigit;
    }
    
    public char getGroupingSeparator() {
        return groupingSeparator;
    }
    
    public void setGroupingSeparator(char groupingSeparator) {
        this.groupingSeparator = groupingSeparator;
    }
    
    public char getDecimalSeparator() {
        return decimalSeparator;
    }
    
    public void setDecimalSeparator(char decimalSeparator) {
        this.decimalSeparator = decimalSeparator;
    }
    
    public char getPerMill() {
        return perMill;
    }
    
    public void setPerMill(char perMill) {
        this.perMill = perMill;
    }
    
    public char getPercent() {
        return percent;
    }
    
    public void setPercent(char percent) {
        this.percent = percent;
    }
    
    public char getDigit() {
        return digit;
    }
    
    public void setDigit(char digit) {
        this.digit = digit;
    }
    
    public char getPatternSeparator() {
        return patternSeparator;
    }
    
    public void setPatternSeparator(char patternSeparator) {
        this.patternSeparator = patternSeparator;
    }
    
    public String getInfinity() {
        return infinity;
    }
    
    public void setInfinity(String infinity) {
        this.infinity = infinity;
    }
    
    public String getNaN() {
        return NaN;
    }
    
    public void setNaN(String NaN) {
        this.NaN = NaN;
    }
    
    public char getMinusSign() {
        return minusSign;
    }
    
    public void setMinusSign(char minusSign) {
        this.minusSign = minusSign;
    }
    
    public String getCurrencySymbol() {
        return currencySymbol;
    }
    
    public void setCurrencySymbol(String currency) {
        currencySymbol = currency;
    }
    
    public String getInternationalCurrencySymbol() {
        return intlCurrencySymbol;
    }
    
    public void setInternationalCurrencySymbol(String currencyCode) {
        intlCurrencySymbol = currencyCode;
        currency = null;
        if (currencyCode != null) {
            try {
                currency = Currency.getInstance(currencyCode);
                currencySymbol = currency.getSymbol();
            } catch (IllegalArgumentException e) {
            }
        }
    }
    
    public Currency getCurrency() {
        return currency;
    }
    
    public void setCurrency(Currency currency) {
        if (currency == null) {
            throw new NullPointerException();
        }
        this.currency = currency;
        intlCurrencySymbol = currency.getCurrencyCode();
        currencySymbol = currency.getSymbol(locale);
    }
    
    public char getMonetaryDecimalSeparator() {
        return monetarySeparator;
    }
    
    public void setMonetaryDecimalSeparator(char sep) {
        monetarySeparator = sep;
    }
    
    char getExponentialSymbol() {
        return exponential;
    }
    
    void setExponentialSymbol(char exp) {
        exponential = exp;
    }
    
    public Object clone() {
        try {
            return (DecimalFormatSymbols)(DecimalFormatSymbols)super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    public boolean equals(Object obj) {
        if (obj == null) return false;
        if (this == obj) return true;
        if (getClass() != obj.getClass()) return false;
        DecimalFormatSymbols other = (DecimalFormatSymbols)(DecimalFormatSymbols)obj;
        return (zeroDigit == other.zeroDigit && groupingSeparator == other.groupingSeparator && decimalSeparator == other.decimalSeparator && percent == other.percent && perMill == other.perMill && digit == other.digit && minusSign == other.minusSign && patternSeparator == other.patternSeparator && infinity.equals(other.infinity) && NaN.equals(other.NaN) && currencySymbol.equals(other.currencySymbol) && intlCurrencySymbol.equals(other.intlCurrencySymbol) && currency == other.currency && monetarySeparator == other.monetarySeparator && locale.equals(other.locale));
    }
    
    public int hashCode() {
        int result = zeroDigit;
        result = result * 37 + groupingSeparator;
        result = result * 37 + decimalSeparator;
        return result;
    }
    
    private void initialize(Locale locale) {
        this.locale = locale;
        boolean needCacheUpdate = false;
        Object[] data = (Object[])(Object[])cachedLocaleData.get(locale);
        if (data == null) {
            data = new Object[3];
            ResourceBundle rb = LocaleData.getLocaleElements(locale);
            data[0] = rb.getStringArray("NumberElements");
            needCacheUpdate = true;
        }
        String[] numberElements = (String[])(String[])data[0];
        ;
        decimalSeparator = numberElements[0].charAt(0);
        groupingSeparator = numberElements[1].charAt(0);
        patternSeparator = numberElements[2].charAt(0);
        percent = numberElements[3].charAt(0);
        zeroDigit = numberElements[4].charAt(0);
        digit = numberElements[5].charAt(0);
        minusSign = numberElements[6].charAt(0);
        exponential = numberElements[7].charAt(0);
        perMill = numberElements[8].charAt(0);
        infinity = numberElements[9];
        NaN = numberElements[10];
        if (!"".equals(locale.getCountry())) {
            try {
                currency = Currency.getInstance(locale);
            } catch (IllegalArgumentException e) {
            }
        }
        if (currency != null) {
            intlCurrencySymbol = currency.getCurrencyCode();
            if (data[1] != null && data[1] == intlCurrencySymbol) {
                currencySymbol = (String)(String)data[2];
            } else {
                currencySymbol = currency.getSymbol(locale);
                data[1] = intlCurrencySymbol;
                data[2] = currencySymbol;
                needCacheUpdate = true;
            }
        } else {
            intlCurrencySymbol = "XXX";
            try {
                currency = Currency.getInstance(intlCurrencySymbol);
            } catch (IllegalArgumentException e) {
            }
            currencySymbol = "\244";
        }
        monetarySeparator = decimalSeparator;
        if (needCacheUpdate) {
            cachedLocaleData.put(locale, data);
        }
    }
    
    private void readObject(ObjectInputStream stream) throws IOException, ClassNotFoundException {
        stream.defaultReadObject();
        if (serialVersionOnStream < 1) {
            monetarySeparator = decimalSeparator;
            exponential = 'E';
        }
        if (serialVersionOnStream < 2) {
            locale = new Locale("");
        }
        serialVersionOnStream = currentSerialVersion;
        if (intlCurrencySymbol != null) {
            try {
                currency = Currency.getInstance(intlCurrencySymbol);
            } catch (IllegalArgumentException e) {
            }
        }
    }
    private char zeroDigit;
    private char groupingSeparator;
    private char decimalSeparator;
    private char perMill;
    private char percent;
    private char digit;
    private char patternSeparator;
    private String infinity;
    private String NaN;
    private char minusSign;
    private String currencySymbol;
    private String intlCurrencySymbol;
    private char monetarySeparator;
    private char exponential;
    private Locale locale;
    private transient Currency currency;
    static final long serialVersionUID = 5772796243397350300L;
    private static final int currentSerialVersion = 2;
    private int serialVersionOnStream = currentSerialVersion;
    private static final Hashtable cachedLocaleData = new Hashtable(3);
}
