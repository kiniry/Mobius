package java.util.zip;

public class CRC32 implements Checksum {
    private int crc;
    
    public CRC32() {
        
    }
    
    public void update(int b) {
        crc = update(crc, b);
    }
    
    public void update(byte[] b, int off, int len) {
        if (b == null) {
            throw new NullPointerException();
        }
        if (off < 0 || len < 0 || off > b.length - len) {
            throw new ArrayIndexOutOfBoundsException();
        }
        crc = updateBytes(crc, b, off, len);
    }
    
    public void update(byte[] b) {
        crc = updateBytes(crc, b, 0, b.length);
    }
    
    public void reset() {
        crc = 0;
    }
    
    public long getValue() {
        return (long)crc & 4294967295L;
    }
    
    private static native int update(int crc, int b);
    
    private static native int updateBytes(int crc, byte[] b, int off, int len);
}
