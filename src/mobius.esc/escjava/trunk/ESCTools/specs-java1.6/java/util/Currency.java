package java.util;

import java.io.Serializable;
import java.security.AccessController;
import sun.text.resources.LocaleData;

public final class Currency implements Serializable {
    private static final long serialVersionUID = -158308464356906721L;
    private final String currencyCode;
    private final transient int defaultFractionDigits;
    private static HashMap instances = new HashMap(7);
    static String mainTable;
    static long[] scCutOverTimes;
    static String[] scOldCurrencies;
    static String[] scNewCurrencies;
    static int[] scOldCurrenciesDFD;
    static int[] scNewCurrenciesDFD;
    static String otherCurrencies;
    static int[] otherCurrenciesDFD;
    private static final int A_TO_Z = ('Z' - 'A') + 1;
    private static final int INVALID_COUNTRY_ENTRY = 127;
    private static final int COUNTRY_WITHOUT_CURRENCY_ENTRY = 128;
    private static final int SIMPLE_CASE_COUNTRY_MASK = 0;
    private static final int SIMPLE_CASE_COUNTRY_FINAL_CHAR_MASK = 31;
    private static final int SIMPLE_CASE_COUNTRY_DEFAULT_DIGITS_MASK = 96;
    private static final int SIMPLE_CASE_COUNTRY_DEFAULT_DIGITS_SHIFT = 5;
    private static final int SPECIAL_CASE_COUNTRY_MASK = 128;
    private static final int SPECIAL_CASE_COUNTRY_INDEX_MASK = 31;
    private static final int SPECIAL_CASE_COUNTRY_INDEX_DELTA = 1;
    private static final int COUNTRY_TYPE_MASK = SIMPLE_CASE_COUNTRY_MASK | SPECIAL_CASE_COUNTRY_MASK;
    static {
        AccessController.doPrivileged(new Currency$1());
    }
    
    private Currency(String currencyCode, int defaultFractionDigits) {
        
        this.currencyCode = currencyCode;
        this.defaultFractionDigits = defaultFractionDigits;
    }
    
    public static Currency getInstance(String currencyCode) {
        return getInstance(currencyCode, Integer.MIN_VALUE);
    }
    
    private static Currency getInstance(String currencyCode, int defaultFractionDigits) {
        synchronized (instances) {
            Currency instance = (Currency)(Currency)instances.get(currencyCode);
            if (instance != null) {
                return instance;
            }
            if (defaultFractionDigits == Integer.MIN_VALUE) {
                if (currencyCode.length() != 3) {
                    throw new IllegalArgumentException();
                }
                char char1 = currencyCode.charAt(0);
                char char2 = currencyCode.charAt(1);
                int tableEntry = getMainTableEntry(char1, char2);
                if ((tableEntry & COUNTRY_TYPE_MASK) == SIMPLE_CASE_COUNTRY_MASK && tableEntry != INVALID_COUNTRY_ENTRY && currencyCode.charAt(2) - 'A' == (tableEntry & SIMPLE_CASE_COUNTRY_FINAL_CHAR_MASK)) {
                    defaultFractionDigits = (tableEntry & SIMPLE_CASE_COUNTRY_DEFAULT_DIGITS_MASK) >> SIMPLE_CASE_COUNTRY_DEFAULT_DIGITS_SHIFT;
                } else {
                    if (currencyCode.charAt(2) == '-') {
                        throw new IllegalArgumentException();
                    }
                    int index = otherCurrencies.indexOf(currencyCode);
                    if (index == -1) {
                        throw new IllegalArgumentException();
                    }
                    defaultFractionDigits = otherCurrenciesDFD[index / 4];
                }
            }
            instance = new Currency(currencyCode, defaultFractionDigits);
            instances.put(currencyCode, instance);
            return instance;
        }
    }
    
    public static Currency getInstance(Locale locale) {
        String country = locale.getCountry();
        if (country == null) {
            throw new NullPointerException();
        }
        if (country.length() != 2) {
            throw new IllegalArgumentException();
        }
        char char1 = country.charAt(0);
        char char2 = country.charAt(1);
        int tableEntry = getMainTableEntry(char1, char2);
        if ((tableEntry & COUNTRY_TYPE_MASK) == SIMPLE_CASE_COUNTRY_MASK && tableEntry != INVALID_COUNTRY_ENTRY) {
            char finalChar = (char)((tableEntry & SIMPLE_CASE_COUNTRY_FINAL_CHAR_MASK) + 'A');
            int defaultFractionDigits = (tableEntry & SIMPLE_CASE_COUNTRY_DEFAULT_DIGITS_MASK) >> SIMPLE_CASE_COUNTRY_DEFAULT_DIGITS_SHIFT;
            StringBuffer sb = new StringBuffer(country);
            sb.append(finalChar);
            return getInstance(sb.toString(), defaultFractionDigits);
        } else {
            if (tableEntry == INVALID_COUNTRY_ENTRY) {
                throw new IllegalArgumentException();
            }
            if (tableEntry == COUNTRY_WITHOUT_CURRENCY_ENTRY) {
                return null;
            } else {
                int index = (tableEntry & SPECIAL_CASE_COUNTRY_INDEX_MASK) - SPECIAL_CASE_COUNTRY_INDEX_DELTA;
                if (scCutOverTimes[index] == Long.MAX_VALUE || System.currentTimeMillis() < scCutOverTimes[index]) {
                    return getInstance(scOldCurrencies[index], scOldCurrenciesDFD[index]);
                } else {
                    return getInstance(scNewCurrencies[index], scNewCurrenciesDFD[index]);
                }
            }
        }
    }
    
    public String getCurrencyCode() {
        return currencyCode;
    }
    
    public String getSymbol() {
        return getSymbol(Locale.getDefault());
    }
    
    public String getSymbol(Locale locale) {
        ResourceBundle bundle;
        try {
            bundle = LocaleData.getLocaleElements(locale);
        } catch (MissingResourceException e) {
            return currencyCode;
        }
        String[][] symbols = (String[][])(String[][])bundle.getObject("CurrencySymbols");
        if (symbols != null) {
            for (int i = 0; i < symbols.length; i++) {
                if (symbols[i][0].equals(currencyCode)) {
                    return symbols[i][1];
                }
            }
        }
        return currencyCode;
    }
    
    public int getDefaultFractionDigits() {
        return defaultFractionDigits;
    }
    
    public String toString() {
        return currencyCode;
    }
    
    private Object readResolve() {
        return getInstance(currencyCode);
    }
    
    private static int getMainTableEntry(char char1, char char2) {
        if (char1 < 'A' || char1 > 'Z' || char2 < 'A' || char2 > 'Z') {
            throw new IllegalArgumentException();
        }
        return mainTable.charAt((char1 - 'A') * A_TO_Z + (char2 - 'A'));
    }
}
