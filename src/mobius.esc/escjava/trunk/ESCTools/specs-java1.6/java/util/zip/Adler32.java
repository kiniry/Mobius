package java.util.zip;

public class Adler32 implements Checksum {
    private int adler = 1;
    
    public Adler32() {
        
    }
    
    public void update(int b) {
        adler = update(adler, b);
    }
    
    public void update(byte[] b, int off, int len) {
        if (b == null) {
            throw new NullPointerException();
        }
        if (off < 0 || len < 0 || off > b.length - len) {
            throw new ArrayIndexOutOfBoundsException();
        }
        adler = updateBytes(adler, b, off, len);
    }
    
    public void update(byte[] b) {
        adler = updateBytes(adler, b, 0, b.length);
    }
    
    public void reset() {
        adler = 1;
    }
    
    public long getValue() {
        return (long)adler & 4294967295L;
    }
    
    private static native int update(int adler, int b);
    
    private static native int updateBytes(int adler, byte[] b, int off, int len);
}
