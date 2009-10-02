package java.text;

import java.util.Locale;
import java.util.MissingResourceException;
import java.util.ResourceBundle;
import sun.misc.SoftCache;
import sun.text.resources.LocaleData;

public abstract class Collator implements java.util.Comparator, Cloneable {
    public static final int PRIMARY = 0;
    public static final int SECONDARY = 1;
    public static final int TERTIARY = 2;
    public static final int IDENTICAL = 3;
    public static final int NO_DECOMPOSITION = 0;
    public static final int CANONICAL_DECOMPOSITION = 1;
    public static final int FULL_DECOMPOSITION = 2;
    
    public static synchronized Collator getInstance() {
        return getInstance(Locale.getDefault());
    }
    
    public static synchronized Collator getInstance(Locale desiredLocale) {
        RuleBasedCollator result = null;
        result = (RuleBasedCollator)(RuleBasedCollator)cache.get(desiredLocale);
        if (result != null) {
            return (Collator)(Collator)result.clone();
        }
        String colString = "";
        int decomp = CANONICAL_DECOMPOSITION;
        try {
            ResourceBundle resource = LocaleData.getLocaleElements(desiredLocale);
            colString = resource.getString("CollationElements");
            decomp = ((Integer)(Integer)resource.getObject("CollationDecomp")).intValue();
        } catch (MissingResourceException e) {
        }
        try {
            result = new RuleBasedCollator(CollationRules.DEFAULTRULES + colString, decomp);
        } catch (ParseException foo) {
            try {
                result = new RuleBasedCollator(CollationRules.DEFAULTRULES);
            } catch (ParseException bar) {
            }
        }
        result.setDecomposition(NO_DECOMPOSITION);
        cache.put(desiredLocale, result);
        return (Collator)(Collator)result.clone();
    }
    
    public abstract int compare(String source, String target);
    
    public int compare(Object o1, Object o2) {
        return compare((String)(String)o1, (String)(String)o2);
    }
    
    public abstract CollationKey getCollationKey(String source);
    
    public boolean equals(String source, String target) {
        return (compare(source, target) == Collator.EQUAL);
    }
    
    public synchronized int getStrength() {
        return strength;
    }
    
    public synchronized void setStrength(int newStrength) {
        if ((newStrength != PRIMARY) && (newStrength != SECONDARY) && (newStrength != TERTIARY) && (newStrength != IDENTICAL)) throw new IllegalArgumentException("Incorrect comparison level.");
        strength = newStrength;
    }
    
    public synchronized int getDecomposition() {
        return decmp;
    }
    
    public synchronized void setDecomposition(int decompositionMode) {
        if ((decompositionMode != NO_DECOMPOSITION) && (decompositionMode != CANONICAL_DECOMPOSITION) && (decompositionMode != FULL_DECOMPOSITION)) throw new IllegalArgumentException("Wrong decomposition mode.");
        decmp = decompositionMode;
    }
    
    public static synchronized Locale[] getAvailableLocales() {
        return LocaleData.getAvailableLocales("CollationElements");
    }
    
    public Object clone() {
        try {
            return (Collator)(Collator)super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    public boolean equals(Object that) {
        if (this == that) return true;
        if (that == null) return false;
        if (getClass() != that.getClass()) return false;
        Collator other = (Collator)(Collator)that;
        return ((strength == other.strength) && (decmp == other.decmp));
    }
    
    public abstract int hashCode();
    
    protected Collator() {
        
        strength = TERTIARY;
        decmp = CANONICAL_DECOMPOSITION;
    }
    private int strength = 0;
    private int decmp = 0;
    private static SoftCache cache = new SoftCache();
    static final int LESS = -1;
    static final int EQUAL = 0;
    static final int GREATER = 1;
}
