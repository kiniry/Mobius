package java.lang;

import java.util.Random;
import sun.misc.FpUtils;

public final class StrictMath {
    
    private StrictMath() {
        
    }
    public static final double E = 2.718281828459045;
    public static final double PI = 3.141592653589793;
    
    public static native double sin(double a);
    
    public static native double cos(double a);
    
    public static native double tan(double a);
    
    public static native double asin(double a);
    
    public static native double acos(double a);
    
    public static native double atan(double a);
    
    public static strictfp double toRadians(double angdeg) {
        return angdeg / 180.0 * PI;
    }
    
    public static strictfp double toDegrees(double angrad) {
        return angrad * 180.0 / PI;
    }
    
    public static native double exp(double a);
    
    public static native double log(double a);
    
    public static native double log10(double a);
    
    public static native double sqrt(double a);
    
    public static native double cbrt(double a);
    
    public static native double IEEEremainder(double f1, double f2);
    
    public static native double ceil(double a);
    
    public static native double floor(double a);
    
    public static double rint(double a) {
        double twoToThe52 = (double)(1L << 52);
        double sign = FpUtils.rawCopySign(1.0, a);
        a = Math.abs(a);
        if (a < twoToThe52) {
            a = ((twoToThe52 + a) - twoToThe52);
        }
        return sign * a;
    }
    
    public static native double atan2(double y, double x);
    
    public static native double pow(double a, double b);
    
    public static int round(float a) {
        return (int)floor(a + 0.5F);
    }
    
    public static long round(double a) {
        return (long)floor(a + 0.5);
    }
    private static Random randomNumberGenerator;
    
    private static synchronized void initRNG() {
        if (randomNumberGenerator == null) randomNumberGenerator = new Random();
    }
    
    public static double random() {
        if (randomNumberGenerator == null) initRNG();
        return randomNumberGenerator.nextDouble();
    }
    
    public static int abs(int a) {
        return (a < 0) ? -a : a;
    }
    
    public static long abs(long a) {
        return (a < 0) ? -a : a;
    }
    
    public static float abs(float a) {
        return (a <= 0.0F) ? 0.0F - a : a;
    }
    
    public static double abs(double a) {
        return (a <= 0.0) ? 0.0 - a : a;
    }
    
    public static int max(int a, int b) {
        return (a >= b) ? a : b;
    }
    
    public static long max(long a, long b) {
        return (a >= b) ? a : b;
    }
    private static long negativeZeroFloatBits = Float.floatToIntBits(-0.0F);
    private static long negativeZeroDoubleBits = Double.doubleToLongBits(-0.0);
    
    public static float max(float a, float b) {
        if (a != a) return a;
        if ((a == 0.0F) && (b == 0.0F) && (Float.floatToIntBits(a) == negativeZeroFloatBits)) {
            return b;
        }
        return (a >= b) ? a : b;
    }
    
    public static double max(double a, double b) {
        if (a != a) return a;
        if ((a == 0.0) && (b == 0.0) && (Double.doubleToLongBits(a) == negativeZeroDoubleBits)) {
            return b;
        }
        return (a >= b) ? a : b;
    }
    
    public static int min(int a, int b) {
        return (a <= b) ? a : b;
    }
    
    public static long min(long a, long b) {
        return (a <= b) ? a : b;
    }
    
    public static float min(float a, float b) {
        if (a != a) return a;
        if ((a == 0.0F) && (b == 0.0F) && (Float.floatToIntBits(b) == negativeZeroFloatBits)) {
            return b;
        }
        return (a <= b) ? a : b;
    }
    
    public static double min(double a, double b) {
        if (a != a) return a;
        if ((a == 0.0) && (b == 0.0) && (Double.doubleToLongBits(b) == negativeZeroDoubleBits)) {
            return b;
        }
        return (a <= b) ? a : b;
    }
    
    public static double ulp(double d) {
        return sun.misc.FpUtils.ulp(d);
    }
    
    public static float ulp(float f) {
        return sun.misc.FpUtils.ulp(f);
    }
    
    public static double signum(double d) {
        return sun.misc.FpUtils.signum(d);
    }
    
    public static float signum(float f) {
        return sun.misc.FpUtils.signum(f);
    }
    
    public static native double sinh(double x);
    
    public static native double cosh(double x);
    
    public static native double tanh(double x);
    
    public static native double hypot(double x, double y);
    
    public static native double expm1(double x);
    
    public static native double log1p(double x);
}
