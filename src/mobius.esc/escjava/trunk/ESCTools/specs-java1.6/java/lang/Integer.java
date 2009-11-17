package java.lang;

public final class Integer extends Number implements Comparable {
    public static final int MIN_VALUE = -2147483648;
    public static final int MAX_VALUE = 2147483647;
    public static final Class TYPE = (Class)Class.getPrimitiveClass("int");
    static final char[] digits = {'0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'};
    
    public static String toString(int i, int radix) {
        if (radix < Character.MIN_RADIX || radix > Character.MAX_RADIX) radix = 10;
        if (radix == 10) {
            return toString(i);
        }
        char[] buf = new char[33];
        boolean negative = (i < 0);
        int charPos = 32;
        if (!negative) {
            i = -i;
        }
        while (i <= -radix) {
            buf[charPos--] = digits[-(i % radix)];
            i = i / radix;
        }
        buf[charPos] = digits[-i];
        if (negative) {
            buf[--charPos] = '-';
        }
        return new String(buf, charPos, (33 - charPos));
    }
    
    public static String toHexString(int i) {
        return toUnsignedString(i, 4);
    }
    
    public static String toOctalString(int i) {
        return toUnsignedString(i, 3);
    }
    
    public static String toBinaryString(int i) {
        return toUnsignedString(i, 1);
    }
    
    private static String toUnsignedString(int i, int shift) {
        char[] buf = new char[32];
        int charPos = 32;
        int radix = 1 << shift;
        int mask = radix - 1;
        do {
            buf[--charPos] = digits[i & mask];
            i >>>= shift;
        }         while (i != 0);
        return new String(buf, charPos, (32 - charPos));
    }
    static final char[] DigitTens = {'0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '2', '2', '2', '2', '2', '2', '2', '2', '2', '2', '3', '3', '3', '3', '3', '3', '3', '3', '3', '3', '4', '4', '4', '4', '4', '4', '4', '4', '4', '4', '5', '5', '5', '5', '5', '5', '5', '5', '5', '5', '6', '6', '6', '6', '6', '6', '6', '6', '6', '6', '7', '7', '7', '7', '7', '7', '7', '7', '7', '7', '8', '8', '8', '8', '8', '8', '8', '8', '8', '8', '9', '9', '9', '9', '9', '9', '9', '9', '9', '9'};
    static final char[] DigitOnes = {'0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9'};
    
    public static String toString(int i) {
        if (i == Integer.MIN_VALUE) return "-2147483648";
        int size = (i < 0) ? stringSize(-i) + 1 : stringSize(i);
        char[] buf = new char[size];
        getChars(i, size, buf);
        return new String(0, size, buf);
    }
    
    static void getChars(int i, int index, char[] buf) {
        int q;
        int r;
        int charPos = index;
        char sign = 0;
        if (i < 0) {
            sign = '-';
            i = -i;
        }
        while (i >= 65536) {
            q = i / 100;
            r = i - ((q << 6) + (q << 5) + (q << 2));
            i = q;
            buf[--charPos] = DigitOnes[r];
            buf[--charPos] = DigitTens[r];
        }
        for (; ; ) {
            q = (i * 52429) >>> (16 + 3);
            r = i - ((q << 3) + (q << 1));
            buf[--charPos] = digits[r];
            i = q;
            if (i == 0) break;
        }
        if (sign != 0) {
            buf[--charPos] = sign;
        }
    }
    static final int[] sizeTable = {9, 99, 999, 9999, 99999, 999999, 9999999, 99999999, 999999999, Integer.MAX_VALUE};
    
    static int stringSize(int x) {
        for (int i = 0; ; i++) if (x <= sizeTable[i]) return i + 1;
    }
    
    public static int parseInt(String s, int radix) throws NumberFormatException {
        if (s == null) {
            throw new NumberFormatException("null");
        }
        if (radix < Character.MIN_RADIX) {
            throw new NumberFormatException("radix " + radix + " less than Character.MIN_RADIX");
        }
        if (radix > Character.MAX_RADIX) {
            throw new NumberFormatException("radix " + radix + " greater than Character.MAX_RADIX");
        }
        int result = 0;
        boolean negative = false;
        int i = 0;
        int max = s.length();
        int limit;
        int multmin;
        int digit;
        if (max > 0) {
            if (s.charAt(0) == '-') {
                negative = true;
                limit = Integer.MIN_VALUE;
                i++;
            } else {
                limit = -Integer.MAX_VALUE;
            }
            multmin = limit / radix;
            if (i < max) {
                digit = Character.digit(s.charAt(i++), radix);
                if (digit < 0) {
                    throw NumberFormatException.forInputString(s);
                } else {
                    result = -digit;
                }
            }
            while (i < max) {
                digit = Character.digit(s.charAt(i++), radix);
                if (digit < 0) {
                    throw NumberFormatException.forInputString(s);
                }
                if (result < multmin) {
                    throw NumberFormatException.forInputString(s);
                }
                result *= radix;
                if (result < limit + digit) {
                    throw NumberFormatException.forInputString(s);
                }
                result -= digit;
            }
        } else {
            throw NumberFormatException.forInputString(s);
        }
        if (negative) {
            if (i > 1) {
                return result;
            } else {
                throw NumberFormatException.forInputString(s);
            }
        } else {
            return -result;
        }
    }
    
    public static int parseInt(String s) throws NumberFormatException {
        return parseInt(s, 10);
    }
    
    public static Integer valueOf(String s, int radix) throws NumberFormatException {
        return new Integer(parseInt(s, radix));
    }
    
    public static Integer valueOf(String s) throws NumberFormatException {
        return new Integer(parseInt(s, 10));
    }
    {
    }
    
    public static Integer valueOf(int i) {
        final int offset = 128;
        if (i >= -128 && i <= 127) {
            return Integer$IntegerCache.cache[i + offset];
        }
        return new Integer(i);
    }
    private final int value;
    
    public Integer(int value) {
        
        this.value = value;
    }
    
    public Integer(String s) throws NumberFormatException {
        
        this.value = parseInt(s, 10);
    }
    
    public byte byteValue() {
        return (byte)value;
    }
    
    public short shortValue() {
        return (short)value;
    }
    
    public int intValue() {
        return value;
    }
    
    public long longValue() {
        return (long)value;
    }
    
    public float floatValue() {
        return (float)value;
    }
    
    public double doubleValue() {
        return (double)value;
    }
    
    public String toString() {
        return String.valueOf(value);
    }
    
    public int hashCode() {
        return value;
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof Integer) {
            return value == ((Integer)(Integer)obj).intValue();
        }
        return false;
    }
    
    public static Integer getInteger(String nm) {
        return getInteger(nm, null);
    }
    
    public static Integer getInteger(String nm, int val) {
        Integer result = getInteger(nm, null);
        return (result == null) ? new Integer(val) : result;
    }
    
    public static Integer getInteger(String nm, Integer val) {
        String v = null;
        try {
            v = System.getProperty(nm);
        } catch (IllegalArgumentException e) {
        } catch (NullPointerException e) {
        }
        if (v != null) {
            try {
                return Integer.decode(v);
            } catch (NumberFormatException e) {
            }
        }
        return val;
    }
    
    public static Integer decode(String nm) throws NumberFormatException {
        int radix = 10;
        int index = 0;
        boolean negative = false;
        Integer result;
        if (nm.startsWith("-")) {
            negative = true;
            index++;
        }
        if (nm.startsWith("0x", index) || nm.startsWith("0X", index)) {
            index += 2;
            radix = 16;
        } else if (nm.startsWith("#", index)) {
            index++;
            radix = 16;
        } else if (nm.startsWith("0", index) && nm.length() > 1 + index) {
            index++;
            radix = 8;
        }
        if (nm.startsWith("-", index)) throw new NumberFormatException("Negative sign in wrong position");
        try {
            result = Integer.valueOf(nm.substring(index), radix);
            result = negative ? new Integer(-result.intValue()) : result;
        } catch (NumberFormatException e) {
            String constant = negative ? new String("-" + nm.substring(index)) : nm.substring(index);
            result = Integer.valueOf(constant, radix);
        }
        return result;
    }
    
    public int compareTo(Integer anotherInteger) {
        int thisVal = this.value;
        int anotherVal = anotherInteger.value;
        return (thisVal < anotherVal ? -1 : (thisVal == anotherVal ? 0 : 1));
    }
    public static final int SIZE = 32;
    
    public static int highestOneBit(int i) {
        i |= (i >> 1);
        i |= (i >> 2);
        i |= (i >> 4);
        i |= (i >> 8);
        i |= (i >> 16);
        return i - (i >>> 1);
    }
    
    public static int lowestOneBit(int i) {
        return i & -i;
    }
    
    public static int numberOfLeadingZeros(int i) {
        if (i == 0) return 32;
        int n = 1;
        if (i >>> 16 == 0) {
            n += 16;
            i <<= 16;
        }
        if (i >>> 24 == 0) {
            n += 8;
            i <<= 8;
        }
        if (i >>> 28 == 0) {
            n += 4;
            i <<= 4;
        }
        if (i >>> 30 == 0) {
            n += 2;
            i <<= 2;
        }
        n -= i >>> 31;
        return n;
    }
    
    public static int numberOfTrailingZeros(int i) {
        int y;
        if (i == 0) return 32;
        int n = 31;
        y = i << 16;
        if (y != 0) {
            n = n - 16;
            i = y;
        }
        y = i << 8;
        if (y != 0) {
            n = n - 8;
            i = y;
        }
        y = i << 4;
        if (y != 0) {
            n = n - 4;
            i = y;
        }
        y = i << 2;
        if (y != 0) {
            n = n - 2;
            i = y;
        }
        return n - ((i << 1) >>> 31);
    }
    
    public static int bitCount(int i) {
        i = i - ((i >>> 1) & 1431655765);
        i = (i & 858993459) + ((i >>> 2) & 858993459);
        i = (i + (i >>> 4)) & 252645135;
        i = i + (i >>> 8);
        i = i + (i >>> 16);
        return i & 63;
    }
    
    public static int rotateLeft(int i, int distance) {
        return (i << distance) | (i >>> -distance);
    }
    
    public static int rotateRight(int i, int distance) {
        return (i >>> distance) | (i << -distance);
    }
    
    public static int reverse(int i) {
        i = (i & 1431655765) << 1 | (i >>> 1) & 1431655765;
        i = (i & 858993459) << 2 | (i >>> 2) & 858993459;
        i = (i & 252645135) << 4 | (i >>> 4) & 252645135;
        i = (i << 24) | ((i & 65280) << 8) | ((i >>> 8) & 65280) | (i >>> 24);
        return i;
    }
    
    public static int signum(int i) {
        return (i >> 31) | (-i >>> 31);
    }
    
    public static int reverseBytes(int i) {
        return ((i >>> 24)) | ((i >> 8) & 65280) | ((i << 8) & 16711680) | ((i << 24));
    }
    private static final long serialVersionUID = 1360826667806852920L;
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((Integer)x0);
    }
}
