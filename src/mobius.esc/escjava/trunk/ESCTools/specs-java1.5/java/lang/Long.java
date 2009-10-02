package java.lang;

public final class Long extends Number implements Comparable {
    public static final long MIN_VALUE = -9223372036854775808L;
    public static final long MAX_VALUE = 9223372036854775807L;
    public static final Class TYPE = (Class)Class.getPrimitiveClass("long");
    
    public static String toString(long i, int radix) {
        if (radix < Character.MIN_RADIX || radix > Character.MAX_RADIX) radix = 10;
        if (radix == 10) return toString(i);
        char[] buf = new char[65];
        int charPos = 64;
        boolean negative = (i < 0);
        if (!negative) {
            i = -i;
        }
        while (i <= -radix) {
            buf[charPos--] = Integer.digits[(int)(-(i % radix))];
            i = i / radix;
        }
        buf[charPos] = Integer.digits[(int)(-i)];
        if (negative) {
            buf[--charPos] = '-';
        }
        return new String(buf, charPos, (65 - charPos));
    }
    
    public static String toHexString(long i) {
        return toUnsignedString(i, 4);
    }
    
    public static String toOctalString(long i) {
        return toUnsignedString(i, 3);
    }
    
    public static String toBinaryString(long i) {
        return toUnsignedString(i, 1);
    }
    
    private static String toUnsignedString(long i, int shift) {
        char[] buf = new char[64];
        int charPos = 64;
        int radix = 1 << shift;
        long mask = radix - 1;
        do {
            buf[--charPos] = Integer.digits[(int)(i & mask)];
            i >>>= shift;
        }         while (i != 0);
        return new String(buf, charPos, (64 - charPos));
    }
    
    public static String toString(long i) {
        if (i == Long.MIN_VALUE) return "-9223372036854775808";
        int size = (i < 0) ? stringSize(-i) + 1 : stringSize(i);
        char[] buf = new char[size];
        getChars(i, size, buf);
        return new String(0, size, buf);
    }
    
    static void getChars(long i, int index, char[] buf) {
        long q;
        int r;
        int charPos = index;
        char sign = 0;
        if (i < 0) {
            sign = '-';
            i = -i;
        }
        while (i > Integer.MAX_VALUE) {
            q = i / 100;
            r = (int)(i - ((q << 6) + (q << 5) + (q << 2)));
            i = q;
            buf[--charPos] = Integer.DigitOnes[r];
            buf[--charPos] = Integer.DigitTens[r];
        }
        int q2;
        int i2 = (int)i;
        while (i2 >= 65536) {
            q2 = i2 / 100;
            r = i2 - ((q2 << 6) + (q2 << 5) + (q2 << 2));
            i2 = q2;
            buf[--charPos] = Integer.DigitOnes[r];
            buf[--charPos] = Integer.DigitTens[r];
        }
        for (; ; ) {
            q2 = (i2 * 52429) >>> (16 + 3);
            r = i2 - ((q2 << 3) + (q2 << 1));
            buf[--charPos] = Integer.digits[r];
            i2 = q2;
            if (i2 == 0) break;
        }
        if (sign != 0) {
            buf[--charPos] = sign;
        }
    }
    
    static int stringSize(long x) {
        long p = 10;
        for (int i = 1; i < 19; i++) {
            if (x < p) return i;
            p = 10 * p;
        }
        return 19;
    }
    
    public static long parseLong(String s, int radix) throws NumberFormatException {
        if (s == null) {
            throw new NumberFormatException("null");
        }
        if (radix < Character.MIN_RADIX) {
            throw new NumberFormatException("radix " + radix + " less than Character.MIN_RADIX");
        }
        if (radix > Character.MAX_RADIX) {
            throw new NumberFormatException("radix " + radix + " greater than Character.MAX_RADIX");
        }
        long result = 0;
        boolean negative = false;
        int i = 0;
        int max = s.length();
        long limit;
        long multmin;
        int digit;
        if (max > 0) {
            if (s.charAt(0) == '-') {
                negative = true;
                limit = Long.MIN_VALUE;
                i++;
            } else {
                limit = -Long.MAX_VALUE;
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
    
    public static long parseLong(String s) throws NumberFormatException {
        return parseLong(s, 10);
    }
    
    public static Long valueOf(String s, int radix) throws NumberFormatException {
        return new Long(parseLong(s, radix));
    }
    
    public static Long valueOf(String s) throws NumberFormatException {
        return new Long(parseLong(s, 10));
    }
    {
    }
    
    public static Long valueOf(long l) {
        final int offset = 128;
        if (l >= -128 && l <= 127) {
            return Long$LongCache.cache[(int)l + offset];
        }
        return new Long(l);
    }
    
    public static Long decode(String nm) throws NumberFormatException {
        int radix = 10;
        int index = 0;
        boolean negative = false;
        Long result;
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
            result = Long.valueOf(nm.substring(index), radix);
            result = negative ? new Long((long)-result.longValue()) : result;
        } catch (NumberFormatException e) {
            String constant = negative ? new String("-" + nm.substring(index)) : nm.substring(index);
            result = Long.valueOf(constant, radix);
        }
        return result;
    }
    private final long value;
    
    public Long(long value) {
        
        this.value = value;
    }
    
    public Long(String s) throws NumberFormatException {
        
        this.value = parseLong(s, 10);
    }
    
    public byte byteValue() {
        return (byte)value;
    }
    
    public short shortValue() {
        return (short)value;
    }
    
    public int intValue() {
        return (int)value;
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
        return (int)(value ^ (value >>> 32));
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof Long) {
            return value == ((Long)(Long)obj).longValue();
        }
        return false;
    }
    
    public static Long getLong(String nm) {
        return getLong(nm, null);
    }
    
    public static Long getLong(String nm, long val) {
        Long result = Long.getLong(nm, null);
        return (result == null) ? new Long(val) : result;
    }
    
    public static Long getLong(String nm, Long val) {
        String v = null;
        try {
            v = System.getProperty(nm);
        } catch (IllegalArgumentException e) {
        } catch (NullPointerException e) {
        }
        if (v != null) {
            try {
                return Long.decode(v);
            } catch (NumberFormatException e) {
            }
        }
        return val;
    }
    
    public int compareTo(Long anotherLong) {
        long thisVal = this.value;
        long anotherVal = anotherLong.value;
        return (thisVal < anotherVal ? -1 : (thisVal == anotherVal ? 0 : 1));
    }
    public static final int SIZE = 64;
    
    public static long highestOneBit(long i) {
        i |= (i >> 1);
        i |= (i >> 2);
        i |= (i >> 4);
        i |= (i >> 8);
        i |= (i >> 16);
        i |= (i >> 32);
        return i - (i >>> 1);
    }
    
    public static long lowestOneBit(long i) {
        return i & -i;
    }
    
    public static int numberOfLeadingZeros(long i) {
        if (i == 0) return 64;
        int n = 1;
        int x = (int)(i >>> 32);
        if (x == 0) {
            n += 32;
            x = (int)i;
        }
        if (x >>> 16 == 0) {
            n += 16;
            x <<= 16;
        }
        if (x >>> 24 == 0) {
            n += 8;
            x <<= 8;
        }
        if (x >>> 28 == 0) {
            n += 4;
            x <<= 4;
        }
        if (x >>> 30 == 0) {
            n += 2;
            x <<= 2;
        }
        n -= x >>> 31;
        return n;
    }
    
    public static int numberOfTrailingZeros(long i) {
        int x;
        int y;
        if (i == 0) return 64;
        int n = 63;
        y = (int)i;
        if (y != 0) {
            n = n - 32;
            x = y;
        } else x = (int)(i >>> 32);
        y = x << 16;
        if (y != 0) {
            n = n - 16;
            x = y;
        }
        y = x << 8;
        if (y != 0) {
            n = n - 8;
            x = y;
        }
        y = x << 4;
        if (y != 0) {
            n = n - 4;
            x = y;
        }
        y = x << 2;
        if (y != 0) {
            n = n - 2;
            x = y;
        }
        return n - ((x << 1) >>> 31);
    }
    
    public static int bitCount(long i) {
        i = i - ((i >>> 1) & 6148914691236517205L);
        i = (i & 3689348814741910323L) + ((i >>> 2) & 3689348814741910323L);
        i = (i + (i >>> 4)) & 1085102592571150095L;
        i = i + (i >>> 8);
        i = i + (i >>> 16);
        i = i + (i >>> 32);
        return (int)i & 127;
    }
    
    public static long rotateLeft(long i, int distance) {
        return (i << distance) | (i >>> -distance);
    }
    
    public static long rotateRight(long i, int distance) {
        return (i >>> distance) | (i << -distance);
    }
    
    public static long reverse(long i) {
        i = (i & 6148914691236517205L) << 1 | (i >>> 1) & 6148914691236517205L;
        i = (i & 3689348814741910323L) << 2 | (i >>> 2) & 3689348814741910323L;
        i = (i & 1085102592571150095L) << 4 | (i >>> 4) & 1085102592571150095L;
        i = (i & 71777214294589695L) << 8 | (i >>> 8) & 71777214294589695L;
        i = (i << 48) | ((i & 4294901760L) << 16) | ((i >>> 16) & 4294901760L) | (i >>> 48);
        return i;
    }
    
    public static int signum(long i) {
        return (int)((i >> 63) | (-i >>> 63));
    }
    
    public static long reverseBytes(long i) {
        i = (i & 71777214294589695L) << 8 | (i >>> 8) & 71777214294589695L;
        return (i << 48) | ((i & 4294901760L) << 16) | ((i >>> 16) & 4294901760L) | (i >>> 48);
    }
    private static final long serialVersionUID = 4290774380558885855L;
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((Long)x0);
    }
}
