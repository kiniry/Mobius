package java.text;

import java.util.ArrayList;

final class MergeCollation {
    
    public MergeCollation(String pattern) throws ParseException {
        
        for (int i = 0; i < statusArray.length; i++) statusArray[i] = 0;
        setPattern(pattern);
    }
    
    public String getPattern() {
        return getPattern(true);
    }
    
    public String getPattern(boolean withWhiteSpace) {
        StringBuffer result = new StringBuffer();
        PatternEntry tmp = null;
        ArrayList extList = null;
        int i;
        for (i = 0; i < patterns.size(); ++i) {
            PatternEntry entry = (PatternEntry)(PatternEntry)patterns.get(i);
            if (entry.extension.length() != 0) {
                if (extList == null) extList = new ArrayList();
                extList.add(entry);
            } else {
                if (extList != null) {
                    PatternEntry last = findLastWithNoExtension(i - 1);
                    for (int j = extList.size() - 1; j >= 0; j--) {
                        tmp = (PatternEntry)((PatternEntry)extList.get(j));
                        tmp.addToBuffer(result, false, withWhiteSpace, last);
                    }
                    extList = null;
                }
                entry.addToBuffer(result, false, withWhiteSpace, null);
            }
        }
        if (extList != null) {
            PatternEntry last = findLastWithNoExtension(i - 1);
            for (int j = extList.size() - 1; j >= 0; j--) {
                tmp = (PatternEntry)((PatternEntry)extList.get(j));
                tmp.addToBuffer(result, false, withWhiteSpace, last);
            }
            extList = null;
        }
        return result.toString();
    }
    
    private final PatternEntry findLastWithNoExtension(int i) {
        for (--i; i >= 0; --i) {
            PatternEntry entry = (PatternEntry)(PatternEntry)patterns.get(i);
            if (entry.extension.length() == 0) {
                return entry;
            }
        }
        return null;
    }
    
    public String emitPattern() {
        return emitPattern(true);
    }
    
    public String emitPattern(boolean withWhiteSpace) {
        StringBuffer result = new StringBuffer();
        for (int i = 0; i < patterns.size(); ++i) {
            PatternEntry entry = (PatternEntry)(PatternEntry)patterns.get(i);
            if (entry != null) {
                entry.addToBuffer(result, true, withWhiteSpace, null);
            }
        }
        return result.toString();
    }
    
    public void setPattern(String pattern) throws ParseException {
        patterns.clear();
        addPattern(pattern);
    }
    
    public void addPattern(String pattern) throws ParseException {
        if (pattern == null) return;
        PatternEntry$Parser parser = new PatternEntry$Parser(pattern);
        PatternEntry entry = parser.next();
        while (entry != null) {
            fixEntry(entry);
            entry = parser.next();
        }
    }
    
    public int getCount() {
        return patterns.size();
    }
    
    public PatternEntry getItemAt(int index) {
        return (PatternEntry)(PatternEntry)patterns.get(index);
    }
    ArrayList patterns = new ArrayList();
    private transient PatternEntry saveEntry = null;
    private transient PatternEntry lastEntry = null;
    private transient StringBuffer excess = new StringBuffer();
    private transient byte[] statusArray = new byte[8192];
    private final byte BITARRAYMASK = (byte)1;
    private final int BYTEPOWER = 3;
    private final int BYTEMASK = (1 << BYTEPOWER) - 1;
    
    private final void fixEntry(PatternEntry newEntry) throws ParseException {
        if (lastEntry != null && newEntry.chars.equals(lastEntry.chars) && newEntry.extension.equals(lastEntry.extension)) {
            if (newEntry.strength != Collator.IDENTICAL && newEntry.strength != PatternEntry.RESET) {
                throw new ParseException("The entries " + lastEntry + " and " + newEntry + " are adjacent in the rules, but have conflicting " + "strengths: A character can\'t be unequal to itself.", -1);
            } else {
                return;
            }
        }
        boolean changeLastEntry = true;
        if (newEntry.strength != PatternEntry.RESET) {
            int oldIndex = -1;
            if (newEntry.chars.length() == 1) {
                char c = newEntry.chars.charAt(0);
                int statusIndex = c >> BYTEPOWER;
                byte bitClump = statusArray[statusIndex];
                byte setBit = (byte)(BITARRAYMASK << (c & BYTEMASK));
                if (bitClump != 0 && (bitClump & setBit) != 0) {
                    oldIndex = patterns.lastIndexOf(newEntry);
                } else {
                    statusArray[statusIndex] = (byte)(bitClump | setBit);
                }
            } else {
                oldIndex = patterns.lastIndexOf(newEntry);
            }
            if (oldIndex != -1) {
                patterns.remove(oldIndex);
            }
            excess.setLength(0);
            int lastIndex = findLastEntry(lastEntry, excess);
            if (excess.length() != 0) {
                newEntry.extension = excess + newEntry.extension;
                if (lastIndex != patterns.size()) {
                    lastEntry = saveEntry;
                    changeLastEntry = false;
                }
            }
            if (lastIndex == patterns.size()) {
                patterns.add(newEntry);
                saveEntry = newEntry;
            } else {
                patterns.add(lastIndex, newEntry);
            }
        }
        if (changeLastEntry) {
            lastEntry = newEntry;
        }
    }
    
    private final int findLastEntry(PatternEntry entry, StringBuffer excessChars) throws ParseException {
        if (entry == null) return 0;
        if (entry.strength != PatternEntry.RESET) {
            int oldIndex = -1;
            if (entry.chars.length() == 1) {
                int index = entry.chars.charAt(0) >> BYTEPOWER;
                if ((statusArray[index] & (BITARRAYMASK << (entry.chars.charAt(0) & BYTEMASK))) != 0) {
                    oldIndex = patterns.lastIndexOf(entry);
                }
            } else {
                oldIndex = patterns.lastIndexOf(entry);
            }
            if (oldIndex == -1) throw new ParseException("couldn\'t find last entry: " + entry, oldIndex);
            return oldIndex + 1;
        } else {
            int i;
            for (i = patterns.size() - 1; i >= 0; --i) {
                PatternEntry e = (PatternEntry)(PatternEntry)patterns.get(i);
                if (e.chars.regionMatches(0, entry.chars, 0, e.chars.length())) {
                    excessChars.append(entry.chars.substring(e.chars.length(), entry.chars.length()));
                    break;
                }
            }
            if (i == -1) throw new ParseException("couldn\'t find: " + entry, i);
            return i + 1;
        }
    }
}
