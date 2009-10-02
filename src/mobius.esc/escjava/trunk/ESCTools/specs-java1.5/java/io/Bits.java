package java.io;

class Bits {
    
    Bits() {
        
    }
    
    static boolean getBoolean(byte[] b, int off) {
        return b[off] != 0;
    }
    
    static char getChar(byte[] b, int off) {
        return (char)(((b[off + 1] & 255) << 0) + ((b[off + 0] & 255) << 8));
    }
    
    static short getShort(byte[] b, int off) {
        return (short)(((b[off + 1] & 255) << 0) + ((b[off + 0] & 255) << 8));
    }
    
    static int getInt(byte[] b, int off) {
        return ((b[off + 3] & 255) << 0) + ((b[off + 2] & 255) << 8) + ((b[off + 1] & 255) << 16) + ((b[off + 0] & 255) << 24);
    }
    
    static float getFloat(byte[] b, int off) {
        int i = ((b[off + 3] & 255) << 0) + ((b[off + 2] & 255) << 8) + ((b[off + 1] & 255) << 16) + ((b[off + 0] & 255) << 24);
        return Float.intBitsToFloat(i);
    }
    
    static long getLong(byte[] b, int off) {
        return ((b[off + 7] & 255L) << 0) + ((b[off + 6] & 255L) << 8) + ((b[off + 5] & 255L) << 16) + ((b[off + 4] & 255L) << 24) + ((b[off + 3] & 255L) << 32) + ((b[off + 2] & 255L) << 40) + ((b[off + 1] & 255L) << 48) + ((b[off + 0] & 255L) << 56);
    }
    
    static double getDouble(byte[] b, int off) {
        long j = ((b[off + 7] & 255L) << 0) + ((b[off + 6] & 255L) << 8) + ((b[off + 5] & 255L) << 16) + ((b[off + 4] & 255L) << 24) + ((b[off + 3] & 255L) << 32) + ((b[off + 2] & 255L) << 40) + ((b[off + 1] & 255L) << 48) + ((b[off + 0] & 255L) << 56);
        return Double.longBitsToDouble(j);
    }
    
    static void putBoolean(byte[] b, int off, boolean val) {
        b[off] = (byte)(val ? 1 : 0);
    }
    
    static void putChar(byte[] b, int off, char val) {
        b[off + 1] = (byte)(val >>> 0);
        b[off + 0] = (byte)(val >>> 8);
    }
    
    static void putShort(byte[] b, int off, short val) {
        b[off + 1] = (byte)(val >>> 0);
        b[off + 0] = (byte)(val >>> 8);
    }
    
    static void putInt(byte[] b, int off, int val) {
        b[off + 3] = (byte)(val >>> 0);
        b[off + 2] = (byte)(val >>> 8);
        b[off + 1] = (byte)(val >>> 16);
        b[off + 0] = (byte)(val >>> 24);
    }
    
    static void putFloat(byte[] b, int off, float val) {
        int i = Float.floatToIntBits(val);
        b[off + 3] = (byte)(i >>> 0);
        b[off + 2] = (byte)(i >>> 8);
        b[off + 1] = (byte)(i >>> 16);
        b[off + 0] = (byte)(i >>> 24);
    }
    
    static void putLong(byte[] b, int off, long val) {
        b[off + 7] = (byte)(val >>> 0);
        b[off + 6] = (byte)(val >>> 8);
        b[off + 5] = (byte)(val >>> 16);
        b[off + 4] = (byte)(val >>> 24);
        b[off + 3] = (byte)(val >>> 32);
        b[off + 2] = (byte)(val >>> 40);
        b[off + 1] = (byte)(val >>> 48);
        b[off + 0] = (byte)(val >>> 56);
    }
    
    static void putDouble(byte[] b, int off, double val) {
        long j = Double.doubleToLongBits(val);
        b[off + 7] = (byte)(j >>> 0);
        b[off + 6] = (byte)(j >>> 8);
        b[off + 5] = (byte)(j >>> 16);
        b[off + 4] = (byte)(j >>> 24);
        b[off + 3] = (byte)(j >>> 32);
        b[off + 2] = (byte)(j >>> 40);
        b[off + 1] = (byte)(j >>> 48);
        b[off + 0] = (byte)(j >>> 56);
    }
}
