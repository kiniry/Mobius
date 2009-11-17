package java.lang;

import sun.misc.FloatingDecimal;
import sun.misc.FpUtils;
import sun.misc.DoubleConsts;

public final class Double extends Number implements Comparable {
    public static final double POSITIVE_INFINITY = 1.0 / 0.0;
    public static final double NEGATIVE_INFINITY = -1.0 / 0.0;
    public static final double NaN = 0.0 / 0.0;
    public static final double MAX_VALUE = 1.7976931348623157E308;
    public static final double MIN_VALUE = 4.9E-324;
    public static final int SIZE = 64;
    public static final Class TYPE = (Class)Class.getPrimitiveClass("double");
    
    public static String toString(double d) {
        return new FloatingDecimal(d).toJavaFormatString();
    }
    
    public static String toHexString(double d) {
        if (!FpUtils.isFinite(d)) return Double.toString(d); else {
            StringBuffer answer = new StringBuffer(24);
            if (FpUtils.rawCopySign(1.0, d) == -1.0) answer.append("-");
            answer.append("0x");
            d = Math.abs(d);
            if (d == 0.0) {
                answer.append("0.0p0");
            } else {
                boolean subnormal = (d < DoubleConsts.MIN_NORMAL);
                long signifBits = (Double.doubleToLongBits(d) & DoubleConsts.SIGNIF_BIT_MASK) | 1152921504606846976L;
                answer.append(subnormal ? "0." : "1.");
                String signif = Long.toHexString(signifBits).substring(3, 16);
                answer.append(signif.equals("0000000000000") ? "0" : signif.replaceFirst("0{1,12}$", ""));
                answer.append("p" + (subnormal ? DoubleConsts.MIN_EXPONENT : FpUtils.getExponent(d)));
            }
            return answer.toString();
        }
    }
    
    public static Double valueOf(String s) throws NumberFormatException {
        return new Double(FloatingDecimal.readJavaFormatString(s).doubleValue());
    }
    
    public static Double valueOf(double d) {
        return new Double(d);
    }
    
    public static double parseDouble(String s) throws NumberFormatException {
        return FloatingDecimal.readJavaFormatString(s).doubleValue();
    }
    
    public static boolean isNaN(double v) {
        return (v != v);
    }
    
    public static boolean isInfinite(double v) {
        return (v == POSITIVE_INFINITY) || (v == NEGATIVE_INFINITY);
    }
    private final double value;
    
    public Double(double value) {
        
        this.value = value;
    }
    
    public Double(String s) throws NumberFormatException {
        this(valueOf(s).doubleValue());
    }
    
    public boolean isNaN() {
        return isNaN(value);
    }
    
    public boolean isInfinite() {
        return isInfinite(value);
    }
    
    public String toString() {
        return String.valueOf(value);
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
    
    public int hashCode() {
        long bits = doubleToLongBits(value);
        return (int)(bits ^ (bits >>> 32));
    }
    
    public boolean equals(Object obj) {
        return (obj instanceof Double) && (doubleToLongBits(((Double)(Double)obj).value) == doubleToLongBits(value));
    }
    
    public static native long doubleToLongBits(double value);
    
    public static native long doubleToRawLongBits(double value);
    
    public static native double longBitsToDouble(long bits);
    
    public int compareTo(Double anotherDouble) {
        return Double.compare(value, anotherDouble.value);
    }
    
    public static int compare(double d1, double d2) {
        if (d1 < d2) return -1;
        if (d1 > d2) return 1;
        long thisBits = Double.doubleToLongBits(d1);
        long anotherBits = Double.doubleToLongBits(d2);
        return (thisBits == anotherBits ? 0 : (thisBits < anotherBits ? -1 : 1));
    }
    private static final long serialVersionUID = -9172774392245257468L;
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((Double)x0);
    }
}
