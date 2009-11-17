package java.text;

import java.util.Vector;
import sun.text.UCompactIntArray;
import sun.text.IntHashtable;
import sun.text.NormalizerImpl;
import sun.text.ComposedCharIter;

final class RBTableBuilder {
    
    public RBTableBuilder(RBCollationTables$BuildAPI tables) {
        
        this.tables = tables;
    }
    
    public void build(String pattern, int decmp) throws ParseException {
        boolean isSource = true;
        int i = 0;
        String expChars;
        String groupChars;
        if (pattern.length() == 0) throw new ParseException("Build rules empty.", 0);
        mapping = new UCompactIntArray((int)RBCollationTables.UNMAPPED);
        pattern = NormalizerImpl.canonicalDecomposeWithSingleQuotation(pattern);
        mPattern = new MergeCollation(pattern);
        int order = 0;
        for (i = 0; i < mPattern.getCount(); ++i) {
            PatternEntry entry = mPattern.getItemAt(i);
            if (entry != null) {
                groupChars = entry.getChars();
                if (groupChars.length() > 1) {
                    switch (groupChars.charAt(groupChars.length() - 1)) {
                    case '@': 
                        frenchSec = true;
                        groupChars = groupChars.substring(0, groupChars.length() - 1);
                        break;
                    
                    case '!': 
                        seAsianSwapping = true;
                        groupChars = groupChars.substring(0, groupChars.length() - 1);
                        break;
                    
                    }
                }
                order = increment(entry.getStrength(), order);
                expChars = entry.getExtension();
                if (expChars.length() != 0) {
                    addExpandOrder(groupChars, expChars, order);
                } else if (groupChars.length() > 1) {
                    char ch = groupChars.charAt(0);
                    if (Character.isHighSurrogate(ch) && groupChars.length() == 2) {
                        addOrder(Character.toCodePoint(ch, groupChars.charAt(1)), order);
                    } else {
                        addContractOrder(groupChars, order);
                    }
                } else {
                    char ch = groupChars.charAt(0);
                    addOrder(ch, order);
                }
            }
        }
        addComposedChars();
        commit();
        mapping.compact();
        tables.fillInTables(frenchSec, seAsianSwapping, mapping, contractTable, expandTable, contractFlags, maxSecOrder, maxTerOrder);
    }
    
    private void addComposedChars() throws ParseException {
        ComposedCharIter iter = new ComposedCharIter();
        int c;
        while ((c = iter.next()) != ComposedCharIter.DONE) {
            if (getCharOrder(c) == RBCollationTables.UNMAPPED) {
                String s = iter.decomposition();
                if (s.length() == 1) {
                    int order = getCharOrder(s.charAt(0));
                    if (order != RBCollationTables.UNMAPPED) {
                        addOrder(c, order);
                    }
                    continue;
                } else if (s.length() == 2) {
                    char ch0 = s.charAt(0);
                    if (Character.isHighSurrogate(ch0)) {
                        int order = getCharOrder(s.codePointAt(0));
                        if (order != RBCollationTables.UNMAPPED) {
                            addOrder(c, order);
                        }
                        continue;
                    }
                }
                int contractOrder = getContractOrder(s);
                if (contractOrder != RBCollationTables.UNMAPPED) {
                    addOrder(c, contractOrder);
                } else {
                    boolean allThere = true;
                    for (int i = 0; i < s.length(); i++) {
                        if (getCharOrder(s.charAt(i)) == RBCollationTables.UNMAPPED) {
                            allThere = false;
                            break;
                        }
                    }
                    if (allThere) {
                        addExpandOrder(c, s, RBCollationTables.UNMAPPED);
                    }
                }
            }
        }
    }
    
    private final void commit() {
        if (expandTable != null) {
            for (int i = 0; i < expandTable.size(); i++) {
                int[] valueList = (int[])(int[])expandTable.elementAt(i);
                for (int j = 0; j < valueList.length; j++) {
                    int order = valueList[j];
                    if (order < RBCollationTables.EXPANDCHARINDEX && order > CHARINDEX) {
                        int ch = order - CHARINDEX;
                        int realValue = getCharOrder(ch);
                        if (realValue == RBCollationTables.UNMAPPED) {
                            valueList[j] = IGNORABLEMASK & ch;
                        } else {
                            valueList[j] = realValue;
                        }
                    }
                }
            }
        }
    }
    
    private final int increment(int aStrength, int lastValue) {
        switch (aStrength) {
        case Collator.PRIMARY: 
            lastValue += PRIMARYORDERINCREMENT;
            lastValue &= RBCollationTables.PRIMARYORDERMASK;
            isOverIgnore = true;
            break;
        
        case Collator.SECONDARY: 
            lastValue += SECONDARYORDERINCREMENT;
            lastValue &= RBCollationTables.SECONDARYDIFFERENCEONLY;
            if (!isOverIgnore) maxSecOrder++;
            break;
        
        case Collator.TERTIARY: 
            lastValue += TERTIARYORDERINCREMENT;
            if (!isOverIgnore) maxTerOrder++;
            break;
        
        }
        return lastValue;
    }
    
    private final void addOrder(int ch, int anOrder) {
        int order = mapping.elementAt(ch);
        if (order >= RBCollationTables.CONTRACTCHARINDEX) {
            int length = 1;
            if (Character.isSupplementaryCodePoint(ch)) {
                length = Character.toChars(ch, keyBuf, 0);
            } else {
                keyBuf[0] = (char)ch;
            }
            addContractOrder(new String(keyBuf, 0, length), anOrder);
        } else {
            mapping.setElementAt(ch, anOrder);
        }
    }
    
    private final void addContractOrder(String groupChars, int anOrder) {
        addContractOrder(groupChars, anOrder, true);
    }
    
    private final void addContractOrder(String groupChars, int anOrder, boolean fwd) {
        if (contractTable == null) {
            contractTable = new Vector(INITIALTABLESIZE);
        }
        int ch = groupChars.codePointAt(0);
        int entry = mapping.elementAt(ch);
        Vector entryTable = getContractValuesImpl(entry - RBCollationTables.CONTRACTCHARINDEX);
        if (entryTable == null) {
            int tableIndex = RBCollationTables.CONTRACTCHARINDEX + contractTable.size();
            entryTable = new Vector(INITIALTABLESIZE);
            contractTable.addElement(entryTable);
            entryTable.addElement(new EntryPair(groupChars.substring(0, Character.charCount(ch)), entry));
            mapping.setElementAt(ch, tableIndex);
        }
        int index = RBCollationTables.getEntry(entryTable, groupChars, fwd);
        if (index != RBCollationTables.UNMAPPED) {
            EntryPair pair = (EntryPair)(EntryPair)entryTable.elementAt(index);
            pair.value = anOrder;
        } else {
            EntryPair pair = (EntryPair)(EntryPair)entryTable.lastElement();
            if (groupChars.length() > pair.entryName.length()) {
                entryTable.addElement(new EntryPair(groupChars, anOrder, fwd));
            } else {
                entryTable.insertElementAt(new EntryPair(groupChars, anOrder, fwd), entryTable.size() - 1);
            }
        }
        if (fwd && groupChars.length() > 1) {
            addContractFlags(groupChars);
            addContractOrder(new StringBuffer(groupChars).reverse().toString(), anOrder, false);
        }
    }
    
    private int getContractOrder(String groupChars) {
        int result = RBCollationTables.UNMAPPED;
        if (contractTable != null) {
            int ch = groupChars.codePointAt(0);
            Vector entryTable = getContractValues(ch);
            if (entryTable != null) {
                int index = RBCollationTables.getEntry(entryTable, groupChars, true);
                if (index != RBCollationTables.UNMAPPED) {
                    EntryPair pair = (EntryPair)(EntryPair)entryTable.elementAt(index);
                    result = pair.value;
                }
            }
        }
        return result;
    }
    
    private final int getCharOrder(int ch) {
        int order = mapping.elementAt(ch);
        if (order >= RBCollationTables.CONTRACTCHARINDEX) {
            Vector groupList = getContractValuesImpl(order - RBCollationTables.CONTRACTCHARINDEX);
            EntryPair pair = (EntryPair)(EntryPair)groupList.firstElement();
            order = pair.value;
        }
        return order;
    }
    
    private Vector getContractValues(int ch) {
        int index = mapping.elementAt(ch);
        return getContractValuesImpl(index - RBCollationTables.CONTRACTCHARINDEX);
    }
    
    private Vector getContractValuesImpl(int index) {
        if (index >= 0) {
            return (Vector)(Vector)contractTable.elementAt(index);
        } else {
            return null;
        }
    }
    
    private final void addExpandOrder(String contractChars, String expandChars, int anOrder) throws ParseException {
        int tableIndex = addExpansion(anOrder, expandChars);
        if (contractChars.length() > 1) {
            char ch = contractChars.charAt(0);
            if (Character.isHighSurrogate(ch) && contractChars.length() == 2) {
                char ch2 = contractChars.charAt(1);
                if (Character.isLowSurrogate(ch2)) {
                    addOrder(Character.toCodePoint(ch, ch2), tableIndex);
                }
            } else {
                addContractOrder(contractChars, tableIndex);
            }
        } else {
            addOrder(contractChars.charAt(0), tableIndex);
        }
    }
    
    private final void addExpandOrder(int ch, String expandChars, int anOrder) throws ParseException {
        int tableIndex = addExpansion(anOrder, expandChars);
        addOrder(ch, tableIndex);
    }
    
    private int addExpansion(int anOrder, String expandChars) {
        if (expandTable == null) {
            expandTable = new Vector(INITIALTABLESIZE);
        }
        int offset = (anOrder == RBCollationTables.UNMAPPED) ? 0 : 1;
        int[] valueList = new int[expandChars.length() + offset];
        if (offset == 1) {
            valueList[0] = anOrder;
        }
        int j = offset;
        for (int i = 0; i < expandChars.length(); i++) {
            char ch0 = expandChars.charAt(i);
            char ch1;
            int ch;
            if (Character.isHighSurrogate(ch0)) {
                if (++i == expandChars.length() || !Character.isLowSurrogate(ch1 = expandChars.charAt(i))) {
                    break;
                }
                ch = Character.toCodePoint(ch0, ch1);
            } else {
                ch = ch0;
            }
            int mapValue = getCharOrder(ch);
            if (mapValue != RBCollationTables.UNMAPPED) {
                valueList[j++] = mapValue;
            } else {
                valueList[j++] = CHARINDEX + ch;
            }
        }
        if (j < valueList.length) {
            int[] tmpBuf = new int[j];
            while (--j >= 0) {
                tmpBuf[j] = valueList[j];
            }
            valueList = tmpBuf;
        }
        int tableIndex = RBCollationTables.EXPANDCHARINDEX + expandTable.size();
        expandTable.addElement(valueList);
        return tableIndex;
    }
    
    private void addContractFlags(String chars) {
        char c0;
        int c;
        int len = chars.length();
        for (int i = 0; i < len; i++) {
            c0 = chars.charAt(i);
            c = Character.isHighSurrogate(c0) ? Character.toCodePoint(c0, chars.charAt(++i)) : c0;
            contractFlags.put(c, 1);
        }
    }
    static final int CHARINDEX = 1879048192;
    private static final int IGNORABLEMASK = 65535;
    private static final int PRIMARYORDERINCREMENT = 65536;
    private static final int SECONDARYORDERINCREMENT = 256;
    private static final int TERTIARYORDERINCREMENT = 1;
    private static final int INITIALTABLESIZE = 20;
    private static final int MAXKEYSIZE = 5;
    private RBCollationTables$BuildAPI tables = null;
    private MergeCollation mPattern = null;
    private boolean isOverIgnore = false;
    private char[] keyBuf = new char[MAXKEYSIZE];
    private IntHashtable contractFlags = new IntHashtable(100);
    private boolean frenchSec = false;
    private boolean seAsianSwapping = false;
    private UCompactIntArray mapping = null;
    private Vector contractTable = null;
    private Vector expandTable = null;
    private short maxSecOrder = 0;
    private short maxTerOrder = 0;
}
