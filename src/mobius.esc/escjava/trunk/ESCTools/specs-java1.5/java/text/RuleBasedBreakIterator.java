package java.text;

import java.io.BufferedInputStream;
import java.io.IOException;
import java.security.AccessController;
import java.security.PrivilegedActionException;
import java.util.MissingResourceException;
import java.text.CharacterIterator;
import java.text.StringCharacterIterator;
import sun.text.CompactByteArray;
import sun.text.SupplementaryCharacterData;

class RuleBasedBreakIterator extends BreakIterator {
    protected static final byte IGNORE = -1;
    private static final short START_STATE = 1;
    private static final short STOP_STATE = 0;
    static final byte[] LABEL = {(byte)'B', (byte)'I', (byte)'d', (byte)'a', (byte)'t', (byte)'a', (byte)'\000'};
    static final int LABEL_LENGTH = LABEL.length;
    static final byte supportedVersion = 1;
    private static final int HEADER_LENGTH = 36;
    private static final int BMP_INDICES_LENGTH = 512;
    private CompactByteArray charCategoryTable = null;
    private SupplementaryCharacterData supplementaryCharCategoryTable = null;
    private short[] stateTable = null;
    private short[] backwardsStateTable = null;
    private boolean[] endStates = null;
    private boolean[] lookaheadStates = null;
    private byte[] additionalData = null;
    private int numCategories;
    private CharacterIterator text = null;
    private long checksum;
    
    public RuleBasedBreakIterator(String datafile) throws IOException, MissingResourceException {
        
        readTables(datafile);
    }
    
    protected void readTables(String datafile) throws IOException, MissingResourceException {
        byte[] buffer = readFile(datafile);
        int stateTableLength = BreakIterator.getInt(buffer, 0);
        int backwardsStateTableLength = BreakIterator.getInt(buffer, 4);
        int endStatesLength = BreakIterator.getInt(buffer, 8);
        int lookaheadStatesLength = BreakIterator.getInt(buffer, 12);
        int BMPdataLength = BreakIterator.getInt(buffer, 16);
        int nonBMPdataLength = BreakIterator.getInt(buffer, 20);
        int additionalDataLength = BreakIterator.getInt(buffer, 24);
        checksum = BreakIterator.getLong(buffer, 28);
        stateTable = new short[stateTableLength];
        int offset = HEADER_LENGTH;
        for (int i = 0; i < stateTableLength; i++, offset += 2) {
            stateTable[i] = BreakIterator.getShort(buffer, offset);
        }
        backwardsStateTable = new short[backwardsStateTableLength];
        for (int i = 0; i < backwardsStateTableLength; i++, offset += 2) {
            backwardsStateTable[i] = BreakIterator.getShort(buffer, offset);
        }
        endStates = new boolean[endStatesLength];
        for (int i = 0; i < endStatesLength; i++, offset++) {
            endStates[i] = buffer[offset] == 1;
        }
        lookaheadStates = new boolean[lookaheadStatesLength];
        for (int i = 0; i < lookaheadStatesLength; i++, offset++) {
            lookaheadStates[i] = buffer[offset] == 1;
        }
        short[] temp1 = new short[BMP_INDICES_LENGTH];
        for (int i = 0; i < BMP_INDICES_LENGTH; i++, offset += 2) {
            temp1[i] = BreakIterator.getShort(buffer, offset);
        }
        byte[] temp2 = new byte[BMPdataLength];
        System.arraycopy(buffer, offset, temp2, 0, BMPdataLength);
        offset += BMPdataLength;
        charCategoryTable = new CompactByteArray(temp1, temp2);
        int[] temp3 = new int[nonBMPdataLength];
        for (int i = 0; i < nonBMPdataLength; i++, offset += 4) {
            temp3[i] = BreakIterator.getInt(buffer, offset);
        }
        supplementaryCharCategoryTable = new SupplementaryCharacterData(temp3);
        if (additionalDataLength > 0) {
            additionalData = new byte[additionalDataLength];
            System.arraycopy(buffer, offset, additionalData, 0, additionalDataLength);
        }
        numCategories = stateTable.length / endStates.length;
    }
    
    protected byte[] readFile(final String datafile) throws IOException, MissingResourceException {
        BufferedInputStream is;
        try {
            is = (BufferedInputStream)(BufferedInputStream)AccessController.doPrivileged(new RuleBasedBreakIterator$1(this, datafile));
        } catch (PrivilegedActionException e) {
            throw new InternalError(e.toString());
        }
        int offset = 0;
        int len = LABEL_LENGTH + 5;
        byte[] buf = new byte[len];
        if (is.read(buf) != len) {
            throw new MissingResourceException("Wrong header length", datafile, "");
        }
        for (int i = 0; i < LABEL_LENGTH; i++, offset++) {
            if (buf[offset] != LABEL[offset]) {
                throw new MissingResourceException("Wrong magic number", datafile, "");
            }
        }
        if (buf[offset] != supportedVersion) {
            throw new MissingResourceException("Unsupported version(" + buf[offset] + ")", datafile, "");
        }
        len = BreakIterator.getInt(buf, ++offset);
        buf = new byte[len];
        if (is.read(buf) != len) {
            throw new MissingResourceException("Wrong data length", datafile, "");
        }
        is.close();
        return buf;
    }
    
    byte[] getAdditionalData() {
        return additionalData;
    }
    
    void setAdditionalData(byte[] b) {
        additionalData = b;
    }
    
    public Object clone() {
        RuleBasedBreakIterator result = (RuleBasedBreakIterator)(RuleBasedBreakIterator)super.clone();
        if (text != null) {
            result.text = (CharacterIterator)(CharacterIterator)text.clone();
        }
        return result;
    }
    
    public boolean equals(Object that) {
        try {
            if (that == null) {
                return false;
            }
            RuleBasedBreakIterator other = (RuleBasedBreakIterator)(RuleBasedBreakIterator)that;
            if (checksum != other.checksum) {
                return false;
            }
            if (text == null) {
                return other.text == null;
            } else {
                return text.equals(other.text);
            }
        } catch (ClassCastException e) {
            return false;
        }
    }
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append('[');
        sb.append("checksum=0x" + Long.toHexString(checksum));
        sb.append(']');
        return sb.toString();
    }
    
    public int hashCode() {
        return (int)checksum;
    }
    
    public int first() {
        CharacterIterator t = getText();
        t.first();
        return t.getIndex();
    }
    
    public int last() {
        CharacterIterator t = getText();
        t.setIndex(t.getEndIndex());
        return t.getIndex();
    }
    
    public int next(int n) {
        int result = current();
        while (n > 0) {
            result = handleNext();
            --n;
        }
        while (n < 0) {
            result = previous();
            ++n;
        }
        return result;
    }
    
    public int next() {
        return handleNext();
    }
    
    public int previous() {
        CharacterIterator text = getText();
        if (current() == text.getBeginIndex()) {
            return BreakIterator.DONE;
        }
        int start = current();
        getPrevious();
        int lastResult = handlePrevious();
        int result = lastResult;
        while (result != BreakIterator.DONE && result < start) {
            lastResult = result;
            result = handleNext();
        }
        text.setIndex(lastResult);
        return lastResult;
    }
    
    private int getPrevious() {
        char c2 = text.previous();
        if (Character.isLowSurrogate(c2) && text.getIndex() > text.getBeginIndex()) {
            char c1 = text.previous();
            if (Character.isHighSurrogate(c1)) {
                return Character.toCodePoint(c1, c2);
            } else {
                text.next();
            }
        }
        return (int)c2;
    }
    
    int getCurrent() {
        char c1 = text.current();
        if (Character.isHighSurrogate(c1) && text.getIndex() < text.getEndIndex()) {
            char c2 = text.next();
            text.previous();
            if (Character.isLowSurrogate(c2)) {
                return Character.toCodePoint(c1, c2);
            }
        }
        return (int)c1;
    }
    
    private int getCurrentCodePointCount() {
        char c1 = text.current();
        if (Character.isHighSurrogate(c1) && text.getIndex() < text.getEndIndex()) {
            char c2 = text.next();
            text.previous();
            if (Character.isLowSurrogate(c2)) {
                return 2;
            }
        }
        return 1;
    }
    
    int getNext() {
        int index = text.getIndex();
        int endIndex = text.getEndIndex();
        if (index == endIndex || (index = index + getCurrentCodePointCount()) >= endIndex) {
            return CharacterIterator.DONE;
        }
        text.setIndex(index);
        return getCurrent();
    }
    
    private int getNextIndex() {
        int index = text.getIndex() + getCurrentCodePointCount();
        int endIndex = text.getEndIndex();
        if (index > endIndex) {
            return endIndex;
        } else {
            return index;
        }
    }
    
    protected static final void checkOffset(int offset, CharacterIterator text) {
        if (offset < text.getBeginIndex() || offset >= text.getEndIndex()) {
            throw new IllegalArgumentException("offset out of bounds");
        }
    }
    
    public int following(int offset) {
        CharacterIterator text = getText();
        checkOffset(offset, text);
        text.setIndex(offset);
        if (offset == text.getBeginIndex()) {
            return handleNext();
        }
        int result = handlePrevious();
        while (result != BreakIterator.DONE && result <= offset) {
            result = handleNext();
        }
        return result;
    }
    
    public int preceding(int offset) {
        CharacterIterator text = getText();
        checkOffset(offset, text);
        text.setIndex(offset);
        return previous();
    }
    
    public boolean isBoundary(int offset) {
        CharacterIterator text = getText();
        checkOffset(offset, text);
        if (offset == text.getBeginIndex()) {
            return true;
        } else {
            return following(offset - 1) == offset;
        }
    }
    
    public int current() {
        return getText().getIndex();
    }
    
    public CharacterIterator getText() {
        if (text == null) {
            text = new StringCharacterIterator("");
        }
        return text;
    }
    
    public void setText(CharacterIterator newText) {
        int end = newText.getEndIndex();
        boolean goodIterator;
        try {
            newText.setIndex(end);
            goodIterator = newText.getIndex() == end;
        } catch (IllegalArgumentException e) {
            goodIterator = false;
        }
        if (goodIterator) {
            text = newText;
        } else {
            text = new RuleBasedBreakIterator$SafeCharIterator(newText);
        }
        text.first();
    }
    
    protected int handleNext() {
        CharacterIterator text = getText();
        if (text.getIndex() == text.getEndIndex()) {
            return BreakIterator.DONE;
        }
        int result = getNextIndex();
        int lookaheadResult = 0;
        int state = START_STATE;
        int category;
        int c = getCurrent();
        while (c != CharacterIterator.DONE && state != STOP_STATE) {
            category = lookupCategory(c);
            if (category != IGNORE) {
                state = lookupState(state, category);
            }
            if (lookaheadStates[state]) {
                if (endStates[state]) {
                    result = lookaheadResult;
                } else {
                    lookaheadResult = getNextIndex();
                }
            } else {
                if (endStates[state]) {
                    result = getNextIndex();
                }
            }
            c = getNext();
        }
        if (c == CharacterIterator.DONE && lookaheadResult == text.getEndIndex()) {
            result = lookaheadResult;
        }
        text.setIndex(result);
        return result;
    }
    
    protected int handlePrevious() {
        CharacterIterator text = getText();
        int state = START_STATE;
        int category = 0;
        int lastCategory = 0;
        int c = getCurrent();
        while (c != CharacterIterator.DONE && state != STOP_STATE) {
            lastCategory = category;
            category = lookupCategory(c);
            if (category != IGNORE) {
                state = lookupBackwardState(state, category);
            }
            c = getPrevious();
        }
        if (c != CharacterIterator.DONE) {
            if (lastCategory != IGNORE) {
                getNext();
                getNext();
            } else {
                getNext();
            }
        }
        return text.getIndex();
    }
    
    protected int lookupCategory(int c) {
        if (c < Character.MIN_SUPPLEMENTARY_CODE_POINT) {
            return charCategoryTable.elementAt((char)c);
        } else {
            return supplementaryCharCategoryTable.getValue(c);
        }
    }
    
    protected int lookupState(int state, int category) {
        return stateTable[state * numCategories + category];
    }
    
    protected int lookupBackwardState(int state, int category) {
        return backwardsStateTable[state * numCategories + category];
    }
    {
    }
}
