package java.lang;

import java.text.BreakIterator;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Locale;
import sun.text.Normalizer;

final class ConditionalSpecialCasing {
    
    ConditionalSpecialCasing() {
        
    }
    static final int FINAL_CASED = 1;
    static final int AFTER_SOFT_DOTTED = 2;
    static final int MORE_ABOVE = 3;
    static final int AFTER_I = 4;
    static final int NOT_BEFORE_DOT = 5;
    static final int COMBINING_CLASS_ABOVE = 230;
    static ConditionalSpecialCasing$Entry[] entry = {new ConditionalSpecialCasing$Entry(931, new char[]{962}, new char[]{931}, null, FINAL_CASED), new ConditionalSpecialCasing$Entry(775, new char[]{775}, new char[]{}, "lt", AFTER_SOFT_DOTTED), new ConditionalSpecialCasing$Entry(73, new char[]{105, 775}, new char[]{73}, "lt", MORE_ABOVE), new ConditionalSpecialCasing$Entry(74, new char[]{106, 775}, new char[]{74}, "lt", MORE_ABOVE), new ConditionalSpecialCasing$Entry(302, new char[]{303, 775}, new char[]{302}, "lt", MORE_ABOVE), new ConditionalSpecialCasing$Entry(204, new char[]{105, 775, 768}, new char[]{204}, "lt", 0), new ConditionalSpecialCasing$Entry(205, new char[]{105, 775, 769}, new char[]{205}, "lt", 0), new ConditionalSpecialCasing$Entry(296, new char[]{105, 775, 771}, new char[]{296}, "lt", 0), new ConditionalSpecialCasing$Entry(775, new char[]{}, new char[]{775}, "tr", AFTER_I), new ConditionalSpecialCasing$Entry(775, new char[]{}, new char[]{775}, "az", AFTER_I), new ConditionalSpecialCasing$Entry(73, new char[]{305}, new char[]{73}, "tr", NOT_BEFORE_DOT), new ConditionalSpecialCasing$Entry(73, new char[]{305}, new char[]{73}, "az", NOT_BEFORE_DOT), new ConditionalSpecialCasing$Entry(105, new char[]{105}, new char[]{304}, "tr", 0), new ConditionalSpecialCasing$Entry(105, new char[]{105}, new char[]{304}, "az", 0)};
    static Hashtable entryTable = new Hashtable();
    static {
        for (int i = 0; i < entry.length; i++) {
            ConditionalSpecialCasing$Entry cur = entry[i];
            Integer cp = new Integer(cur.getCodePoint());
            HashSet set = (HashSet)(HashSet)entryTable.get(cp);
            if (set == null) {
                set = new HashSet();
            }
            set.add(cur);
            entryTable.put(cp, set);
        }
    }
    
    static int toLowerCaseEx(String src, int index, Locale locale) {
        char[] result = lookUpTable(src, index, locale, true);
        if (result != null) {
            if (result.length == 1) {
                return result[0];
            } else {
                return Character.ERROR;
            }
        } else {
            return Character.toLowerCase(src.codePointAt(index));
        }
    }
    
    static int toUpperCaseEx(String src, int index, Locale locale) {
        char[] result = lookUpTable(src, index, locale, false);
        if (result != null) {
            if (result.length == 1) {
                return result[0];
            } else {
                return Character.ERROR;
            }
        } else {
            return Character.toUpperCaseEx(src.codePointAt(index));
        }
    }
    
    static char[] toLowerCaseCharArray(String src, int index, Locale locale) {
        return lookUpTable(src, index, locale, true);
    }
    
    static char[] toUpperCaseCharArray(String src, int index, Locale locale) {
        char[] result = lookUpTable(src, index, locale, false);
        if (result != null) {
            return result;
        } else {
            return Character.toUpperCaseCharArray(src.codePointAt(index));
        }
    }
    
    private static char[] lookUpTable(String src, int index, Locale locale, boolean bLowerCasing) {
        HashSet set = (HashSet)(HashSet)entryTable.get(new Integer(src.codePointAt(index)));
        if (set != null) {
            Iterator iter = set.iterator();
            String currentLang = locale.getLanguage();
            while (iter.hasNext()) {
                ConditionalSpecialCasing$Entry entry = (ConditionalSpecialCasing$Entry)(ConditionalSpecialCasing$Entry)iter.next();
                String conditionLang = entry.getLanguage();
                if (((conditionLang == null) || (conditionLang.equals(currentLang))) && isConditionMet(src, index, locale, entry.getCondition())) {
                    return (bLowerCasing ? entry.getLowerCase() : entry.getUpperCase());
                }
            }
        }
        return null;
    }
    
    private static boolean isConditionMet(String src, int index, Locale locale, int condition) {
        switch (condition) {
        case FINAL_CASED: 
            return isFinalCased(src, index, locale);
        
        case AFTER_SOFT_DOTTED: 
            return isAfterSoftDotted(src, index);
        
        case MORE_ABOVE: 
            return isMoreAbove(src, index);
        
        case AFTER_I: 
            return isAfterI(src, index);
        
        case NOT_BEFORE_DOT: 
            return !isBeforeDot(src, index);
        
        default: 
            return true;
        
        }
    }
    
    private static boolean isFinalCased(String src, int index, Locale locale) {
        BreakIterator wordBoundary = BreakIterator.getWordInstance(locale);
        wordBoundary.setText(src);
        int ch;
        for (int i = index; (i >= 0) && !wordBoundary.isBoundary(i); i -= Character.charCount(ch)) {
            ch = src.codePointBefore(i);
            if (isCased(ch)) {
                int len = src.length();
                for (i = index + Character.charCount(src.codePointAt(index)); (i < len) && !wordBoundary.isBoundary(i); i += Character.charCount(ch)) {
                    ch = src.codePointAt(i);
                    if (isCased(ch)) {
                        return false;
                    }
                }
                return true;
            }
        }
        return false;
    }
    
    private static boolean isAfterI(String src, int index) {
        int ch;
        int cc;
        for (int i = index; i > 0; i -= Character.charCount(ch)) {
            ch = src.codePointBefore(i);
            if (ch == 'I') {
                return true;
            } else {
                cc = Normalizer.getClass(ch);
                if ((cc == 0) || (cc == COMBINING_CLASS_ABOVE)) {
                    return false;
                }
            }
        }
        return false;
    }
    
    private static boolean isAfterSoftDotted(String src, int index) {
        int ch;
        int cc;
        for (int i = index; i > 0; i -= Character.charCount(ch)) {
            ch = src.codePointBefore(i);
            if (isSoftDotted(ch)) {
                return true;
            } else {
                cc = Normalizer.getClass(ch);
                if ((cc == 0) || (cc == COMBINING_CLASS_ABOVE)) {
                    return false;
                }
            }
        }
        return false;
    }
    
    private static boolean isMoreAbove(String src, int index) {
        int ch;
        int cc;
        int len = src.length();
        for (int i = index + Character.charCount(src.codePointAt(index)); i < len; i += Character.charCount(ch)) {
            ch = src.codePointAt(i);
            cc = Normalizer.getClass(ch);
            if (cc == COMBINING_CLASS_ABOVE) {
                return true;
            } else if (cc == 0) {
                return false;
            }
        }
        return false;
    }
    
    private static boolean isBeforeDot(String src, int index) {
        int ch;
        int cc;
        int len = src.length();
        for (int i = index + Character.charCount(src.codePointAt(index)); i < len; i += Character.charCount(ch)) {
            ch = src.codePointAt(i);
            if (ch == '\u0307') {
                return true;
            } else {
                cc = Normalizer.getClass(ch);
                if ((cc == 0) || (cc == COMBINING_CLASS_ABOVE)) {
                    return false;
                }
            }
        }
        return false;
    }
    
    private static boolean isCased(int ch) {
        int type = Character.getType(ch);
        if (type == Character.LOWERCASE_LETTER || type == Character.UPPERCASE_LETTER || type == Character.TITLECASE_LETTER) {
            return true;
        } else {
            if ((ch >= 688) && (ch <= 696)) {
                return true;
            } else if ((ch >= 704) && (ch <= 705)) {
                return true;
            } else if ((ch >= 736) && (ch <= 740)) {
                return true;
            } else if (ch == 837) {
                return true;
            } else if (ch == 890) {
                return true;
            } else if ((ch >= 7468) && (ch <= 7521)) {
                return true;
            } else if ((ch >= 8544) && (ch <= 8575)) {
                return true;
            } else if ((ch >= 9398) && (ch <= 9449)) {
                return true;
            } else {
                return false;
            }
        }
    }
    
    private static boolean isSoftDotted(int ch) {
        switch (ch) {
        case 105: 
        
        case 106: 
        
        case 303: 
        
        case 616: 
        
        case 1110: 
        
        case 1112: 
        
        case 7522: 
        
        case 7725: 
        
        case 7883: 
        
        case 8305: 
            return true;
        
        default: 
            return false;
        
        }
    }
    {
    }
}
