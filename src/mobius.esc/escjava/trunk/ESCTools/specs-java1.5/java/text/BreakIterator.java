package java.text;

import java.util.Locale;
import java.util.ResourceBundle;
import sun.text.resources.LocaleData;
import java.text.CharacterIterator;
import java.text.StringCharacterIterator;
import java.lang.ref.SoftReference;
import java.security.AccessController;

public abstract class BreakIterator implements Cloneable {
    
    protected BreakIterator() {
        
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    public static final int DONE = -1;
    
    public abstract int first();
    
    public abstract int last();
    
    public abstract int next(int n);
    
    public abstract int next();
    
    public abstract int previous();
    
    public abstract int following(int offset);
    
    public int preceding(int offset) {
        int pos = following(offset);
        while (pos >= offset && pos != DONE) pos = previous();
        return pos;
    }
    
    public boolean isBoundary(int offset) {
        if (offset == 0) return true; else return following(offset - 1) == offset;
    }
    
    public abstract int current();
    
    public abstract CharacterIterator getText();
    
    public void setText(String newText) {
        setText(new StringCharacterIterator(newText));
    }
    
    public abstract void setText(CharacterIterator newText);
    private static final int CHARACTER_INDEX = 0;
    private static final int WORD_INDEX = 1;
    private static final int LINE_INDEX = 2;
    private static final int SENTENCE_INDEX = 3;
    private static final SoftReference[] iterCache = new SoftReference[4];
    
    public static BreakIterator getWordInstance() {
        return getWordInstance(Locale.getDefault());
    }
    
    public static BreakIterator getWordInstance(Locale where) {
        return getBreakInstance(where, WORD_INDEX, "WordData", "WordDictionary");
    }
    
    public static BreakIterator getLineInstance() {
        return getLineInstance(Locale.getDefault());
    }
    
    public static BreakIterator getLineInstance(Locale where) {
        return getBreakInstance(where, LINE_INDEX, "LineData", "LineDictionary");
    }
    
    public static BreakIterator getCharacterInstance() {
        return getCharacterInstance(Locale.getDefault());
    }
    
    public static BreakIterator getCharacterInstance(Locale where) {
        return getBreakInstance(where, CHARACTER_INDEX, "CharacterData", "CharacterDictionary");
    }
    
    public static BreakIterator getSentenceInstance() {
        return getSentenceInstance(Locale.getDefault());
    }
    
    public static BreakIterator getSentenceInstance(Locale where) {
        return getBreakInstance(where, SENTENCE_INDEX, "SentenceData", "SentenceDictionary");
    }
    
    private static BreakIterator getBreakInstance(Locale where, int type, String dataName, String dictionaryName) {
        if (iterCache[type] != null) {
            BreakIterator$BreakIteratorCache cache = (BreakIterator$BreakIteratorCache)(BreakIterator$BreakIteratorCache)iterCache[type].get();
            if (cache != null) {
                if (cache.getLocale().equals(where)) {
                    return cache.createBreakInstance();
                }
            }
        }
        BreakIterator result = createBreakInstance(where, type, dataName, dictionaryName);
        BreakIterator$BreakIteratorCache cache = new BreakIterator$BreakIteratorCache(where, result);
        iterCache[type] = new SoftReference(cache);
        return result;
    }
    
    private static ResourceBundle getBundle(final String baseName, final Locale locale) {
        return (ResourceBundle)(ResourceBundle)AccessController.doPrivileged(new BreakIterator$1(baseName, locale));
    }
    
    private static BreakIterator createBreakInstance(Locale where, int type, String dataName, String dictionaryName) {
        ResourceBundle bundle = getBundle("sun.text.resources.BreakIteratorInfo", where);
        String[] classNames = bundle.getStringArray("BreakIteratorClasses");
        String dataFile = bundle.getString(dataName);
        try {
            if (classNames[type].equals("RuleBasedBreakIterator")) {
                return new RuleBasedBreakIterator(dataFile);
            } else if (classNames[type].equals("DictionaryBasedBreakIterator")) {
                String dictionaryFile = bundle.getString(dictionaryName);
                return new DictionaryBasedBreakIterator(dataFile, dictionaryFile);
            } else {
                throw new IllegalArgumentException("Invalid break iterator class \"" + classNames[type] + "\"");
            }
        } catch (Exception e) {
            throw new InternalError(e.toString());
        }
    }
    
    public static synchronized Locale[] getAvailableLocales() {
        return LocaleData.getAvailableLocales("NumberPatterns");
    }
    {
    }
    
    protected static long getLong(byte[] buf, int offset) {
        long num = buf[offset] & 255;
        for (int i = 1; i < 8; i++) {
            num = num << 8 | (buf[offset + i] & 255);
        }
        return num;
    }
    
    protected static int getInt(byte[] buf, int offset) {
        int num = buf[offset] & 255;
        for (int i = 1; i < 4; i++) {
            num = num << 8 | (buf[offset + i] & 255);
        }
        return num;
    }
    
    protected static short getShort(byte[] buf, int offset) {
        short num = (short)(buf[offset] & 255);
        num = (short)(num << 8 | (buf[offset + 1] & 255));
        return num;
    }
}
