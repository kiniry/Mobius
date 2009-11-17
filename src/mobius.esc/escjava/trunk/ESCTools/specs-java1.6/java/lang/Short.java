package java.lang;

public final class Short extends Number implements Comparable {
    public static final short MIN_VALUE = -32768;
    public static final short MAX_VALUE = 32767;
    public static final Class TYPE = (Class)Class.getPrimitiveClass("short");
    
    public static String toString(short s) {
        return Integer.toString((int)s, 10);
    }
    
    public static short parseShort(String s) throws NumberFormatException {
        return parseShort(s, 10);
    }
    
    public static short parseShort(String s, int radix) throws NumberFormatException {
        int i = Integer.parseInt(s, radix);
        if (i < MIN_VALUE || i > MAX_VALUE) throw new NumberFormatException("Value out of range. Value:\"" + s + "\" Radix:" + radix);
        return (short)i;
    }
    
    public static Short valueOf(String s, int radix) throws NumberFormatException {
        return new Short(parseShort(s, radix));
    }
    
    public static Short valueOf(String s) throws NumberFormatException {
        return valueOf(s, 10);
    }
    {
    }
    
    public static Short valueOf(short s) {
        final int offset = 128;
        int sAsInt = s;
        if (sAsInt >= -128 && sAsInt <= 127) {
            return Short$ShortCache.cache[sAsInt + offset];
        }
        return new Short(s);
    }
    
    public static Short decode(String nm) throws NumberFormatException {
        int radix = 10;
        int index = 0;
        boolean negative = false;
        Short result;
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
            result = Short.valueOf(nm.substring(index), radix);
            result = negative ? new Short((short)-result.shortValue()) : result;
        } catch (NumberFormatException e) {
            String constant = negative ? new String("-" + nm.substring(index)) : nm.substring(index);
            result = Short.valueOf(constant, radix);
        }
        return result;
    }
    private final short value;
    
    public Short(short value) {
        
        this.value = value;
    }
    
    public Short(String s) throws NumberFormatException {
        
        this.value = parseShort(s, 10);
    }
    
    public byte byteValue() {
        return (byte)value;
    }
    
    public short shortValue() {
        return value;
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
        return String.valueOf((int)value);
    }
    
    public int hashCode() {
        return (int)value;
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof Short) {
            return value == ((Short)(Short)obj).shortValue();
        }
        return false;
    }
    
    public int compareTo(Short anotherShort) {
        return this.value - anotherShort.value;
    }
    public static final int SIZE = 16;
    
    public static short reverseBytes(short i) {
        return (short)(((i & 65280) >> 8) | (i << 8));
    }
    private static final long serialVersionUID = 7515723908773894738L;
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((Short)x0);
    }
}
