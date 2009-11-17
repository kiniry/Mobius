package java.text;

import java.lang.Character;
import java.util.Vector;
import sun.text.Normalizer;
import sun.text.NormalizerUtilities;

public final class CollationElementIterator {
    public static final int NULLORDER = -1;
    
    CollationElementIterator(String sourceText, RuleBasedCollator owner) {
        
        this.owner = owner;
        ordering = owner.getTables();
        if (sourceText.length() != 0) {
            Normalizer$Mode mode = NormalizerUtilities.toNormalizerMode(owner.getDecomposition());
            text = new Normalizer(sourceText, mode);
        }
    }
    
    CollationElementIterator(CharacterIterator sourceText, RuleBasedCollator owner) {
        
        this.owner = owner;
        ordering = owner.getTables();
        Normalizer$Mode mode = NormalizerUtilities.toNormalizerMode(owner.getDecomposition());
        text = new Normalizer(sourceText, mode);
    }
    
    public void reset() {
        if (text != null) {
            text.reset();
            Normalizer$Mode mode = NormalizerUtilities.toNormalizerMode(owner.getDecomposition());
            text.setMode(mode);
        }
        buffer = null;
        expIndex = 0;
        swapOrder = 0;
    }
    
    public int next() {
        if (text == null) {
            return NULLORDER;
        }
        Normalizer$Mode textMode = text.getMode();
        Normalizer$Mode ownerMode = NormalizerUtilities.toNormalizerMode(owner.getDecomposition());
        if (textMode != ownerMode) {
            text.setMode(ownerMode);
        }
        if (buffer != null) {
            if (expIndex < buffer.length) {
                return strengthOrder(buffer[expIndex++]);
            } else {
                buffer = null;
                expIndex = 0;
            }
        } else if (swapOrder != 0) {
            if (Character.isSupplementaryCodePoint(swapOrder)) {
                char[] chars = Character.toChars(swapOrder);
                swapOrder = chars[1];
                return chars[0] << 16;
            }
            int order = swapOrder << 16;
            swapOrder = 0;
            return order;
        }
        int ch = text.next();
        if (ch == Normalizer.DONE) {
            return NULLORDER;
        }
        int value = ordering.getUnicodeOrder(ch);
        if (value == RuleBasedCollator.UNMAPPED) {
            swapOrder = ch;
            return UNMAPPEDCHARVALUE;
        } else if (value >= RuleBasedCollator.CONTRACTCHARINDEX) {
            value = nextContractChar(ch);
        }
        if (value >= RuleBasedCollator.EXPANDCHARINDEX) {
            buffer = ordering.getExpandValueList(value);
            expIndex = 0;
            value = buffer[expIndex++];
        }
        if (ordering.isSEAsianSwapping()) {
            int consonant;
            if (isThaiPreVowel(ch)) {
                consonant = text.next();
                if (isThaiBaseConsonant(consonant)) {
                    buffer = makeReorderedBuffer(consonant, value, buffer, true);
                    value = buffer[0];
                    expIndex = 1;
                } else {
                    text.previous();
                }
            }
            if (isLaoPreVowel(ch)) {
                consonant = text.next();
                if (isLaoBaseConsonant(consonant)) {
                    buffer = makeReorderedBuffer(consonant, value, buffer, true);
                    value = buffer[0];
                    expIndex = 1;
                } else {
                    text.previous();
                }
            }
        }
        return strengthOrder(value);
    }
    
    public int previous() {
        if (text == null) {
            return NULLORDER;
        }
        Normalizer$Mode textMode = text.getMode();
        Normalizer$Mode ownerMode = NormalizerUtilities.toNormalizerMode(owner.getDecomposition());
        if (textMode != ownerMode) {
            text.setMode(ownerMode);
        }
        if (buffer != null) {
            if (expIndex > 0) {
                return strengthOrder(buffer[--expIndex]);
            } else {
                buffer = null;
                expIndex = 0;
            }
        } else if (swapOrder != 0) {
            if (Character.isSupplementaryCodePoint(swapOrder)) {
                char[] chars = Character.toChars(swapOrder);
                swapOrder = chars[1];
                return chars[0] << 16;
            }
            int order = swapOrder << 16;
            swapOrder = 0;
            return order;
        }
        int ch = text.previous();
        if (ch == Normalizer.DONE) {
            return NULLORDER;
        }
        int value = ordering.getUnicodeOrder(ch);
        if (value == RuleBasedCollator.UNMAPPED) {
            swapOrder = UNMAPPEDCHARVALUE;
            return ch;
        } else if (value >= RuleBasedCollator.CONTRACTCHARINDEX) {
            value = prevContractChar(ch);
        }
        if (value >= RuleBasedCollator.EXPANDCHARINDEX) {
            buffer = ordering.getExpandValueList(value);
            expIndex = buffer.length;
            value = buffer[--expIndex];
        }
        if (ordering.isSEAsianSwapping()) {
            int vowel;
            if (isThaiBaseConsonant(ch)) {
                vowel = text.previous();
                if (isThaiPreVowel(vowel)) {
                    buffer = makeReorderedBuffer(vowel, value, buffer, false);
                    expIndex = buffer.length - 1;
                    value = buffer[expIndex];
                } else {
                    text.next();
                }
            }
            if (isLaoBaseConsonant(ch)) {
                vowel = text.previous();
                if (isLaoPreVowel(vowel)) {
                    buffer = makeReorderedBuffer(vowel, value, buffer, false);
                    expIndex = buffer.length - 1;
                    value = buffer[expIndex];
                } else {
                    text.next();
                }
            }
        }
        return strengthOrder(value);
    }
    
    public static final int primaryOrder(int order) {
        order &= RBCollationTables.PRIMARYORDERMASK;
        return (order >>> RBCollationTables.PRIMARYORDERSHIFT);
    }
    
    public static final short secondaryOrder(int order) {
        order = order & RBCollationTables.SECONDARYORDERMASK;
        return ((short)(order >> RBCollationTables.SECONDARYORDERSHIFT));
    }
    
    public static final short tertiaryOrder(int order) {
        return ((short)(order &= RBCollationTables.TERTIARYORDERMASK));
    }
    
    final int strengthOrder(int order) {
        int s = owner.getStrength();
        if (s == Collator.PRIMARY) {
            order &= RBCollationTables.PRIMARYDIFFERENCEONLY;
        } else if (s == Collator.SECONDARY) {
            order &= RBCollationTables.SECONDARYDIFFERENCEONLY;
        }
        return order;
    }
    
    public void setOffset(int newOffset) {
        if (text != null) {
            if (newOffset < text.getBeginIndex() || newOffset >= text.getEndIndex()) {
                text.setIndexOnly(newOffset);
            } else {
                int c = text.setIndex(newOffset);
                if (ordering.usedInContractSeq(c)) {
                    while (ordering.usedInContractSeq(c)) {
                        c = text.previous();
                    }
                    int last = text.getIndex();
                    while (text.getIndex() <= newOffset) {
                        last = text.getIndex();
                        next();
                    }
                    text.setIndexOnly(last);
                }
            }
        }
        buffer = null;
        expIndex = 0;
        swapOrder = 0;
    }
    
    public int getOffset() {
        return (text != null) ? text.getIndex() : 0;
    }
    
    public int getMaxExpansion(int order) {
        return ordering.getMaxExpansion(order);
    }
    
    public void setText(String source) {
        buffer = null;
        swapOrder = 0;
        expIndex = 0;
        Normalizer$Mode mode = NormalizerUtilities.toNormalizerMode(owner.getDecomposition());
        if (text == null) {
            text = new Normalizer(source, mode);
        } else {
            text.setMode(mode);
            text.setText(source);
        }
    }
    
    public void setText(CharacterIterator source) {
        buffer = null;
        swapOrder = 0;
        expIndex = 0;
        Normalizer$Mode mode = NormalizerUtilities.toNormalizerMode(owner.getDecomposition());
        if (text == null) {
            text = new Normalizer(source, mode);
        } else {
            text.setMode(mode);
            text.setText(source);
        }
    }
    
    private static final boolean isThaiPreVowel(int ch) {
        return (ch >= 3648) && (ch <= 3652);
    }
    
    private static final boolean isThaiBaseConsonant(int ch) {
        return (ch >= 3585) && (ch <= 3630);
    }
    
    private static final boolean isLaoPreVowel(int ch) {
        return (ch >= 3776) && (ch <= 3780);
    }
    
    private static final boolean isLaoBaseConsonant(int ch) {
        return (ch >= 3713) && (ch <= 3758);
    }
    
    private int[] makeReorderedBuffer(int colFirst, int lastValue, int[] lastExpansion, boolean forward) {
        int[] result;
        int firstValue = ordering.getUnicodeOrder(colFirst);
        if (firstValue >= RuleBasedCollator.CONTRACTCHARINDEX) {
            firstValue = forward ? nextContractChar(colFirst) : prevContractChar(colFirst);
        }
        int[] firstExpansion = null;
        if (firstValue >= RuleBasedCollator.EXPANDCHARINDEX) {
            firstExpansion = ordering.getExpandValueList(firstValue);
        }
        if (!forward) {
            int temp1 = firstValue;
            firstValue = lastValue;
            lastValue = temp1;
            int[] temp2 = firstExpansion;
            firstExpansion = lastExpansion;
            lastExpansion = temp2;
        }
        if (firstExpansion == null && lastExpansion == null) {
            result = new int[2];
            result[0] = firstValue;
            result[1] = lastValue;
        } else {
            int firstLength = firstExpansion == null ? 1 : firstExpansion.length;
            int lastLength = lastExpansion == null ? 1 : lastExpansion.length;
            result = new int[firstLength + lastLength];
            if (firstExpansion == null) {
                result[0] = firstValue;
            } else {
                System.arraycopy(firstExpansion, 0, result, 0, firstLength);
            }
            if (lastExpansion == null) {
                result[firstLength] = lastValue;
            } else {
                System.arraycopy(lastExpansion, 0, result, firstLength, lastLength);
            }
        }
        return result;
    }
    
    static final boolean isIgnorable(int order) {
        return ((primaryOrder(order) == 0) ? true : false);
    }
    
    private int nextContractChar(int ch) {
        Vector list = ordering.getContractValues(ch);
        EntryPair pair = (EntryPair)(EntryPair)list.firstElement();
        int order = pair.value;
        pair = (EntryPair)(EntryPair)list.lastElement();
        int maxLength = pair.entryName.length();
        Normalizer tempText = (Normalizer)(Normalizer)text.clone();
        tempText.previous();
        key.setLength(0);
        int c = tempText.next();
        while (maxLength > 0 && c != Normalizer.DONE) {
            if (Character.isSupplementaryCodePoint(c)) {
                key.append(Character.toChars(c));
                maxLength -= 2;
            } else {
                key.append((char)c);
                --maxLength;
            }
            c = tempText.next();
        }
        String fragment = key.toString();
        maxLength = 1;
        for (int i = list.size() - 1; i > 0; i--) {
            pair = (EntryPair)(EntryPair)list.elementAt(i);
            if (!pair.fwd) continue;
            if (fragment.startsWith(pair.entryName) && pair.entryName.length() > maxLength) {
                maxLength = pair.entryName.length();
                order = pair.value;
            }
        }
        while (maxLength > 1) {
            c = text.next();
            maxLength -= Character.charCount(c);
        }
        return order;
    }
    
    private int prevContractChar(int ch) {
        Vector list = ordering.getContractValues(ch);
        EntryPair pair = (EntryPair)(EntryPair)list.firstElement();
        int order = pair.value;
        pair = (EntryPair)(EntryPair)list.lastElement();
        int maxLength = pair.entryName.length();
        Normalizer tempText = (Normalizer)(Normalizer)text.clone();
        tempText.next();
        key.setLength(0);
        int c = tempText.previous();
        while (maxLength > 0 && c != Normalizer.DONE) {
            if (Character.isSupplementaryCodePoint(c)) {
                key.append(Character.toChars(c));
                maxLength -= 2;
            } else {
                key.append((char)c);
                --maxLength;
            }
            c = tempText.previous();
        }
        String fragment = key.toString();
        maxLength = 1;
        for (int i = list.size() - 1; i > 0; i--) {
            pair = (EntryPair)(EntryPair)list.elementAt(i);
            if (pair.fwd) continue;
            if (fragment.startsWith(pair.entryName) && pair.entryName.length() > maxLength) {
                maxLength = pair.entryName.length();
                order = pair.value;
            }
        }
        while (maxLength > 1) {
            c = text.previous();
            maxLength -= Character.charCount(c);
        }
        return order;
    }
    static final int UNMAPPEDCHARVALUE = 2147418112;
    private Normalizer text = null;
    private int[] buffer = null;
    private int expIndex = 0;
    private StringBuffer key = new StringBuffer(5);
    private int swapOrder = 0;
    private RBCollationTables ordering;
    private RuleBasedCollator owner;
}
