package java.util;

import java.io.*;

public class BitSet implements Cloneable, java.io.Serializable {
    private static final int ADDRESS_BITS_PER_UNIT = 6;
    private static final int BITS_PER_UNIT = 1 << ADDRESS_BITS_PER_UNIT;
    private static final int BIT_INDEX_MASK = BITS_PER_UNIT - 1;
    private static final long WORD_MASK = -1L;
    private long[] bits;
    private transient int unitsInUse = 0;
    private static final long serialVersionUID = 7997698588986878753L;
    
    private static int unitIndex(int bitIndex) {
        return bitIndex >> ADDRESS_BITS_PER_UNIT;
    }
    
    private static long bit(int bitIndex) {
        return 1L << (bitIndex & BIT_INDEX_MASK);
    }
    
    private void recalculateUnitsInUse() {
        int i;
        for (i = unitsInUse - 1; i >= 0; i--) if (bits[i] != 0) break;
        unitsInUse = i + 1;
    }
    
    public BitSet() {
        this(BITS_PER_UNIT);
    }
    
    public BitSet(int nbits) {
        
        if (nbits < 0) throw new NegativeArraySizeException("nbits < 0: " + nbits);
        bits = new long[(unitIndex(nbits - 1) + 1)];
    }
    
    private void ensureCapacity(int unitsRequired) {
        if (bits.length < unitsRequired) {
            int request = Math.max(2 * bits.length, unitsRequired);
            long[] newBits = new long[request];
            System.arraycopy(bits, 0, newBits, 0, unitsInUse);
            bits = newBits;
        }
    }
    
    public void flip(int bitIndex) {
        if (bitIndex < 0) throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);
        int unitIndex = unitIndex(bitIndex);
        int unitsRequired = unitIndex + 1;
        if (unitsInUse < unitsRequired) {
            ensureCapacity(unitsRequired);
            bits[unitIndex] ^= bit(bitIndex);
            unitsInUse = unitsRequired;
        } else {
            bits[unitIndex] ^= bit(bitIndex);
            if (bits[unitsInUse - 1] == 0) recalculateUnitsInUse();
        }
    }
    
    public void flip(int fromIndex, int toIndex) {
        if (fromIndex < 0) throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        if (toIndex < 0) throw new IndexOutOfBoundsException("toIndex < 0: " + toIndex);
        if (fromIndex > toIndex) throw new IndexOutOfBoundsException("fromIndex: " + fromIndex + " > toIndex: " + toIndex);
        int endUnitIndex = unitIndex(toIndex);
        int unitsRequired = endUnitIndex + 1;
        if (unitsInUse < unitsRequired) {
            ensureCapacity(unitsRequired);
            unitsInUse = unitsRequired;
        }
        int startUnitIndex = unitIndex(fromIndex);
        long bitMask = 0;
        if (startUnitIndex == endUnitIndex) {
            bitMask = (1L << (toIndex & BIT_INDEX_MASK)) - (1L << (fromIndex & BIT_INDEX_MASK));
            bits[startUnitIndex] ^= bitMask;
            if (bits[unitsInUse - 1] == 0) recalculateUnitsInUse();
            return;
        }
        bitMask = bitsLeftOf(fromIndex & BIT_INDEX_MASK);
        bits[startUnitIndex] ^= bitMask;
        if (endUnitIndex - startUnitIndex > 1) {
            for (int i = startUnitIndex + 1; i < endUnitIndex; i++) bits[i] ^= WORD_MASK;
        }
        bitMask = bitsRightOf(toIndex & BIT_INDEX_MASK);
        bits[endUnitIndex] ^= bitMask;
        if (bits[unitsInUse - 1] == 0) recalculateUnitsInUse();
    }
    
    private static long bitsRightOf(int x) {
        return (x == 0 ? 0 : WORD_MASK >>> (64 - x));
    }
    
    private static long bitsLeftOf(int x) {
        return WORD_MASK << x;
    }
    
    public void set(int bitIndex) {
        if (bitIndex < 0) throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);
        int unitIndex = unitIndex(bitIndex);
        int unitsRequired = unitIndex + 1;
        if (unitsInUse < unitsRequired) {
            ensureCapacity(unitsRequired);
            bits[unitIndex] |= bit(bitIndex);
            unitsInUse = unitsRequired;
        } else {
            bits[unitIndex] |= bit(bitIndex);
        }
    }
    
    public void set(int bitIndex, boolean value) {
        if (value) set(bitIndex); else clear(bitIndex);
    }
    
    public void set(int fromIndex, int toIndex) {
        if (fromIndex < 0) throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        if (toIndex < 0) throw new IndexOutOfBoundsException("toIndex < 0: " + toIndex);
        if (fromIndex > toIndex) throw new IndexOutOfBoundsException("fromIndex: " + fromIndex + " > toIndex: " + toIndex);
        int endUnitIndex = unitIndex(toIndex);
        int unitsRequired = endUnitIndex + 1;
        if (unitsInUse < unitsRequired) {
            ensureCapacity(unitsRequired);
            unitsInUse = unitsRequired;
        }
        int startUnitIndex = unitIndex(fromIndex);
        long bitMask = 0;
        if (startUnitIndex == endUnitIndex) {
            bitMask = (1L << (toIndex & BIT_INDEX_MASK)) - (1L << (fromIndex & BIT_INDEX_MASK));
            bits[startUnitIndex] |= bitMask;
            return;
        }
        bitMask = bitsLeftOf(fromIndex & BIT_INDEX_MASK);
        bits[startUnitIndex] |= bitMask;
        if (endUnitIndex - startUnitIndex > 1) {
            for (int i = startUnitIndex + 1; i < endUnitIndex; i++) bits[i] |= WORD_MASK;
        }
        bitMask = bitsRightOf(toIndex & BIT_INDEX_MASK);
        bits[endUnitIndex] |= bitMask;
    }
    
    public void set(int fromIndex, int toIndex, boolean value) {
        if (value) set(fromIndex, toIndex); else clear(fromIndex, toIndex);
    }
    
    public void clear(int bitIndex) {
        if (bitIndex < 0) throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);
        int unitIndex = unitIndex(bitIndex);
        if (unitIndex >= unitsInUse) return;
        bits[unitIndex] &= ~bit(bitIndex);
        if (bits[unitsInUse - 1] == 0) recalculateUnitsInUse();
    }
    
    public void clear(int fromIndex, int toIndex) {
        if (fromIndex < 0) throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        if (toIndex < 0) throw new IndexOutOfBoundsException("toIndex < 0: " + toIndex);
        if (fromIndex > toIndex) throw new IndexOutOfBoundsException("fromIndex: " + fromIndex + " > toIndex: " + toIndex);
        int startUnitIndex = unitIndex(fromIndex);
        if (startUnitIndex >= unitsInUse) return;
        int endUnitIndex = unitIndex(toIndex);
        long bitMask = 0;
        if (startUnitIndex == endUnitIndex) {
            bitMask = (1L << (toIndex & BIT_INDEX_MASK)) - (1L << (fromIndex & BIT_INDEX_MASK));
            bits[startUnitIndex] &= ~bitMask;
            if (bits[unitsInUse - 1] == 0) recalculateUnitsInUse();
            return;
        }
        bitMask = bitsLeftOf(fromIndex & BIT_INDEX_MASK);
        bits[startUnitIndex] &= ~bitMask;
        if (endUnitIndex - startUnitIndex > 1) {
            for (int i = startUnitIndex + 1; i < endUnitIndex; i++) {
                if (i < unitsInUse) bits[i] = 0;
            }
        }
        if (endUnitIndex < unitsInUse) {
            bitMask = bitsRightOf(toIndex & BIT_INDEX_MASK);
            bits[endUnitIndex] &= ~bitMask;
        }
        if (bits[unitsInUse - 1] == 0) recalculateUnitsInUse();
    }
    
    public void clear() {
        while (unitsInUse > 0) bits[--unitsInUse] = 0;
    }
    
    public boolean get(int bitIndex) {
        if (bitIndex < 0) throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);
        boolean result = false;
        int unitIndex = unitIndex(bitIndex);
        if (unitIndex < unitsInUse) result = ((bits[unitIndex] & bit(bitIndex)) != 0);
        return result;
    }
    
    public BitSet get(int fromIndex, int toIndex) {
        if (fromIndex < 0) throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        if (toIndex < 0) throw new IndexOutOfBoundsException("toIndex < 0: " + toIndex);
        if (fromIndex > toIndex) throw new IndexOutOfBoundsException("fromIndex: " + fromIndex + " > toIndex: " + toIndex);
        if (length() <= fromIndex || fromIndex == toIndex) return new BitSet(0);
        if (length() < toIndex) toIndex = length();
        BitSet result = new BitSet(toIndex - fromIndex);
        int startBitIndex = fromIndex & BIT_INDEX_MASK;
        int endBitIndex = toIndex & BIT_INDEX_MASK;
        int targetWords = (toIndex - fromIndex + 63) / 64;
        int sourceWords = unitIndex(toIndex) - unitIndex(fromIndex) + 1;
        int inverseIndex = 64 - startBitIndex;
        int targetIndex = 0;
        int sourceIndex = unitIndex(fromIndex);
        while (targetIndex < targetWords - 1) result.bits[targetIndex++] = (bits[sourceIndex++] >>> startBitIndex) | ((inverseIndex == 64) ? 0 : bits[sourceIndex] << inverseIndex);
        result.bits[targetIndex] = (sourceWords == targetWords ? (bits[sourceIndex] & bitsRightOf(endBitIndex)) >>> startBitIndex : (bits[sourceIndex++] >>> startBitIndex) | ((inverseIndex == 64) ? 0 : (getBits(sourceIndex) & bitsRightOf(endBitIndex)) << inverseIndex));
        result.unitsInUse = targetWords;
        result.recalculateUnitsInUse();
        return result;
    }
    
    private long getBits(int j) {
        return (j < unitsInUse) ? bits[j] : 0;
    }
    
    public int nextSetBit(int fromIndex) {
        if (fromIndex < 0) throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        int u = unitIndex(fromIndex);
        if (u >= unitsInUse) return -1;
        int testIndex = (fromIndex & BIT_INDEX_MASK);
        long unit = bits[u] >> testIndex;
        if (unit == 0) testIndex = 0;
        while ((unit == 0) && (u < unitsInUse - 1)) unit = bits[++u];
        if (unit == 0) return -1;
        testIndex += trailingZeroCnt(unit);
        return ((u * BITS_PER_UNIT) + testIndex);
    }
    
    private static int trailingZeroCnt(long val) {
        int byteVal = (int)val & 255;
        if (byteVal != 0) return trailingZeroTable[byteVal];
        byteVal = (int)(val >>> 8) & 255;
        if (byteVal != 0) return trailingZeroTable[byteVal] + 8;
        byteVal = (int)(val >>> 16) & 255;
        if (byteVal != 0) return trailingZeroTable[byteVal] + 16;
        byteVal = (int)(val >>> 24) & 255;
        if (byteVal != 0) return trailingZeroTable[byteVal] + 24;
        byteVal = (int)(val >>> 32) & 255;
        if (byteVal != 0) return trailingZeroTable[byteVal] + 32;
        byteVal = (int)(val >>> 40) & 255;
        if (byteVal != 0) return trailingZeroTable[byteVal] + 40;
        byteVal = (int)(val >>> 48) & 255;
        if (byteVal != 0) return trailingZeroTable[byteVal] + 48;
        byteVal = (int)(val >>> 56) & 255;
        return trailingZeroTable[byteVal] + 56;
    }
    private static final byte[] trailingZeroTable = {-25, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 6, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 7, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 6, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0};
    
    public int nextClearBit(int fromIndex) {
        if (fromIndex < 0) throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        int u = unitIndex(fromIndex);
        if (u >= unitsInUse) return fromIndex;
        int testIndex = (fromIndex & BIT_INDEX_MASK);
        long unit = bits[u] >> testIndex;
        if (unit == (WORD_MASK >> testIndex)) testIndex = 0;
        while ((unit == WORD_MASK) && (u < unitsInUse - 1)) unit = bits[++u];
        if (unit == WORD_MASK) return length();
        if (unit == 0) return u * BITS_PER_UNIT + testIndex;
        testIndex += trailingZeroCnt(~unit);
        return ((u * BITS_PER_UNIT) + testIndex);
    }
    
    public int length() {
        if (unitsInUse == 0) return 0;
        long highestUnit = bits[unitsInUse - 1];
        int highPart = (int)(highestUnit >>> 32);
        return 64 * (unitsInUse - 1) + (highPart == 0 ? bitLen((int)highestUnit) : 32 + bitLen((int)highPart));
    }
    
    private static int bitLen(int w) {
        return (w < 1 << 15 ? (w < 1 << 7 ? (w < 1 << 3 ? (w < 1 << 1 ? (w < 1 << 0 ? (w < 0 ? 32 : 0) : 1) : (w < 1 << 2 ? 2 : 3)) : (w < 1 << 5 ? (w < 1 << 4 ? 4 : 5) : (w < 1 << 6 ? 6 : 7))) : (w < 1 << 11 ? (w < 1 << 9 ? (w < 1 << 8 ? 8 : 9) : (w < 1 << 10 ? 10 : 11)) : (w < 1 << 13 ? (w < 1 << 12 ? 12 : 13) : (w < 1 << 14 ? 14 : 15)))) : (w < 1 << 23 ? (w < 1 << 19 ? (w < 1 << 17 ? (w < 1 << 16 ? 16 : 17) : (w < 1 << 18 ? 18 : 19)) : (w < 1 << 21 ? (w < 1 << 20 ? 20 : 21) : (w < 1 << 22 ? 22 : 23))) : (w < 1 << 27 ? (w < 1 << 25 ? (w < 1 << 24 ? 24 : 25) : (w < 1 << 26 ? 26 : 27)) : (w < 1 << 29 ? (w < 1 << 28 ? 28 : 29) : (w < 1 << 30 ? 30 : 31)))));
    }
    
    public boolean isEmpty() {
        return (unitsInUse == 0);
    }
    
    public boolean intersects(BitSet set) {
        for (int i = Math.min(unitsInUse, set.unitsInUse) - 1; i >= 0; i--) if ((bits[i] & set.bits[i]) != 0) return true;
        return false;
    }
    
    public int cardinality() {
        int sum = 0;
        for (int i = 0; i < unitsInUse; i++) sum += bitCount(bits[i]);
        return sum;
    }
    
    private static int bitCount(long val) {
        val -= (val & -6148914691236517206L) >>> 1;
        val = (val & 3689348814741910323L) + ((val >>> 2) & 3689348814741910323L);
        val = (val + (val >>> 4)) & 1085102592571150095L;
        val += val >>> 8;
        val += val >>> 16;
        return ((int)(val) + (int)(val >>> 32)) & 255;
    }
    
    public void and(BitSet set) {
        if (this == set) return;
        int oldUnitsInUse = unitsInUse;
        unitsInUse = Math.min(unitsInUse, set.unitsInUse);
        int i;
        for (i = 0; i < unitsInUse; i++) bits[i] &= set.bits[i];
        for (; i < oldUnitsInUse; i++) bits[i] = 0;
        if (unitsInUse > 0 && bits[unitsInUse - 1] == 0) recalculateUnitsInUse();
    }
    
    public void or(BitSet set) {
        if (this == set) return;
        ensureCapacity(set.unitsInUse);
        int unitsInCommon = Math.min(unitsInUse, set.unitsInUse);
        int i;
        for (i = 0; i < unitsInCommon; i++) bits[i] |= set.bits[i];
        for (; i < set.unitsInUse; i++) bits[i] = set.bits[i];
        if (unitsInUse < set.unitsInUse) unitsInUse = set.unitsInUse;
    }
    
    public void xor(BitSet set) {
        int unitsInCommon;
        if (unitsInUse >= set.unitsInUse) {
            unitsInCommon = set.unitsInUse;
        } else {
            unitsInCommon = unitsInUse;
            int newUnitsInUse = set.unitsInUse;
            ensureCapacity(newUnitsInUse);
            unitsInUse = newUnitsInUse;
        }
        int i;
        for (i = 0; i < unitsInCommon; i++) bits[i] ^= set.bits[i];
        for (; i < set.unitsInUse; i++) bits[i] = set.bits[i];
        recalculateUnitsInUse();
    }
    
    public void andNot(BitSet set) {
        int unitsInCommon = Math.min(unitsInUse, set.unitsInUse);
        for (int i = 0; i < unitsInCommon; i++) {
            bits[i] &= ~set.bits[i];
        }
        recalculateUnitsInUse();
    }
    
    public int hashCode() {
        long h = 1234;
        for (int i = bits.length; --i >= 0; ) h ^= bits[i] * (i + 1);
        return (int)((h >> 32) ^ h);
    }
    
    public int size() {
        return bits.length << ADDRESS_BITS_PER_UNIT;
    }
    
    public boolean equals(Object obj) {
        if (!(obj instanceof BitSet)) return false;
        if (this == obj) return true;
        BitSet set = (BitSet)(BitSet)obj;
        int minUnitsInUse = Math.min(unitsInUse, set.unitsInUse);
        for (int i = 0; i < minUnitsInUse; i++) if (bits[i] != set.bits[i]) return false;
        if (unitsInUse > minUnitsInUse) {
            for (int i = minUnitsInUse; i < unitsInUse; i++) if (bits[i] != 0) return false;
        } else {
            for (int i = minUnitsInUse; i < set.unitsInUse; i++) if (set.bits[i] != 0) return false;
        }
        return true;
    }
    
    public Object clone() {
        BitSet result = null;
        try {
            result = (BitSet)(BitSet)super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
        result.bits = new long[bits.length];
        System.arraycopy(bits, 0, result.bits, 0, unitsInUse);
        return result;
    }
    
    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        unitsInUse = bits.length;
        recalculateUnitsInUse();
    }
    
    public String toString() {
        int numBits = unitsInUse << ADDRESS_BITS_PER_UNIT;
        StringBuffer buffer = new StringBuffer(8 * numBits + 2);
        String separator = "";
        buffer.append('{');
        for (int i = 0; i < numBits; i++) {
            if (get(i)) {
                buffer.append(separator);
                separator = ", ";
                buffer.append(i);
            }
        }
        buffer.append('}');
        return buffer.toString();
    }
}
