package java.text;

import java.io.*;
import java.security.AccessController;
import java.security.PrivilegedActionException;
import java.util.MissingResourceException;
import sun.text.CompactByteArray;
import sun.text.SupplementaryCharacterData;

class BreakDictionary {
    private static int supportedVersion = 1;
    private CompactByteArray columnMap = null;
    private SupplementaryCharacterData supplementaryCharColumnMap = null;
    private int numCols;
    private int numColGroups;
    private short[] table = null;
    private short[] rowIndex = null;
    private int[] rowIndexFlags = null;
    private short[] rowIndexFlagsIndex = null;
    private byte[] rowIndexShifts = null;
    
    public BreakDictionary(String dictionaryName) throws IOException, MissingResourceException {
        
        readDictionaryFile(dictionaryName);
    }
    
    private void readDictionaryFile(final String dictionaryName) throws IOException, MissingResourceException {
        BufferedInputStream in;
        try {
            in = (BufferedInputStream)(BufferedInputStream)AccessController.doPrivileged(new BreakDictionary$1(this, dictionaryName));
        } catch (PrivilegedActionException e) {
            throw new InternalError(e.toString());
        }
        byte[] buf = new byte[8];
        if (in.read(buf) != 8) {
            throw new MissingResourceException("Wrong data length", dictionaryName, "");
        }
        int version = BreakIterator.getInt(buf, 0);
        if (version != supportedVersion) {
            throw new MissingResourceException("Dictionary version(" + version + ") is unsupported", dictionaryName, "");
        }
        int len = BreakIterator.getInt(buf, 4);
        buf = new byte[len];
        if (in.read(buf) != len) {
            throw new MissingResourceException("Wrong data length", dictionaryName, "");
        }
        in.close();
        int l;
        int offset = 0;
        l = BreakIterator.getInt(buf, offset);
        offset += 4;
        short[] temp = new short[l];
        for (int i = 0; i < l; i++, offset += 2) {
            temp[i] = BreakIterator.getShort(buf, offset);
        }
        l = BreakIterator.getInt(buf, offset);
        offset += 4;
        byte[] temp2 = new byte[l];
        for (int i = 0; i < l; i++, offset++) {
            temp2[i] = buf[offset];
        }
        columnMap = new CompactByteArray(temp, temp2);
        numCols = BreakIterator.getInt(buf, offset);
        offset += 4;
        numColGroups = BreakIterator.getInt(buf, offset);
        offset += 4;
        l = BreakIterator.getInt(buf, offset);
        offset += 4;
        rowIndex = new short[l];
        for (int i = 0; i < l; i++, offset += 2) {
            rowIndex[i] = BreakIterator.getShort(buf, offset);
        }
        l = BreakIterator.getInt(buf, offset);
        offset += 4;
        rowIndexFlagsIndex = new short[l];
        for (int i = 0; i < l; i++, offset += 2) {
            rowIndexFlagsIndex[i] = BreakIterator.getShort(buf, offset);
        }
        l = BreakIterator.getInt(buf, offset);
        offset += 4;
        rowIndexFlags = new int[l];
        for (int i = 0; i < l; i++, offset += 4) {
            rowIndexFlags[i] = BreakIterator.getInt(buf, offset);
        }
        l = BreakIterator.getInt(buf, offset);
        offset += 4;
        rowIndexShifts = new byte[l];
        for (int i = 0; i < l; i++, offset++) {
            rowIndexShifts[i] = buf[offset];
        }
        l = BreakIterator.getInt(buf, offset);
        offset += 4;
        table = new short[l];
        for (int i = 0; i < l; i++, offset += 2) {
            table[i] = BreakIterator.getShort(buf, offset);
        }
        l = BreakIterator.getInt(buf, offset);
        offset += 4;
        int[] temp3 = new int[l];
        for (int i = 0; i < l; i++, offset += 4) {
            temp3[i] = BreakIterator.getInt(buf, offset);
        }
        supplementaryCharColumnMap = new SupplementaryCharacterData(temp3);
    }
    
    public final short getNextStateFromCharacter(int row, int ch) {
        int col;
        if (ch < Character.MIN_SUPPLEMENTARY_CODE_POINT) {
            col = columnMap.elementAt((char)ch);
        } else {
            col = supplementaryCharColumnMap.getValue(ch);
        }
        return getNextState(row, col);
    }
    
    public final short getNextState(int row, int col) {
        if (cellIsPopulated(row, col)) {
            return internalAt(rowIndex[row], col + rowIndexShifts[row]);
        } else {
            return 0;
        }
    }
    
    private final boolean cellIsPopulated(int row, int col) {
        if (rowIndexFlagsIndex[row] < 0) {
            return col == -rowIndexFlagsIndex[row];
        } else {
            int flags = rowIndexFlags[rowIndexFlagsIndex[row] + (col >> 5)];
            return (flags & (1 << (col & 31))) != 0;
        }
    }
    
    private final short internalAt(int row, int col) {
        return table[row * numCols + col];
    }
}
