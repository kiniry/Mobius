package java.util.zip;

public class Inflater {
    private long strm;
    private byte[] buf = new byte[0];
    private int off;
    private int len;
    private boolean finished;
    private boolean needDict;
    static {
        initIDs();
    }
    
    public Inflater(boolean nowrap) {
        
        strm = init(nowrap);
    }
    
    public Inflater() {
        this(false);
    }
    
    public synchronized void setInput(byte[] b, int off, int len) {
        if (b == null) {
            throw new NullPointerException();
        }
        if (off < 0 || len < 0 || off > b.length - len) {
            throw new ArrayIndexOutOfBoundsException();
        }
        this.buf = b;
        this.off = off;
        this.len = len;
    }
    
    public void setInput(byte[] b) {
        setInput(b, 0, b.length);
    }
    
    public synchronized void setDictionary(byte[] b, int off, int len) {
        if (strm == 0 || b == null) {
            throw new NullPointerException();
        }
        if (off < 0 || len < 0 || off > b.length - len) {
            throw new ArrayIndexOutOfBoundsException();
        }
        setDictionary(strm, b, off, len);
        needDict = false;
    }
    
    public void setDictionary(byte[] b) {
        setDictionary(b, 0, b.length);
    }
    
    public synchronized int getRemaining() {
        return len;
    }
    
    public synchronized boolean needsInput() {
        return len <= 0;
    }
    
    public synchronized boolean needsDictionary() {
        return needDict;
    }
    
    public synchronized boolean finished() {
        return finished;
    }
    
    public synchronized int inflate(byte[] b, int off, int len) throws DataFormatException {
        if (b == null) {
            throw new NullPointerException();
        }
        if (off < 0 || len < 0 || off > b.length - len) {
            throw new ArrayIndexOutOfBoundsException();
        }
        return inflateBytes(b, off, len);
    }
    
    public int inflate(byte[] b) throws DataFormatException {
        return inflate(b, 0, b.length);
    }
    
    public synchronized int getAdler() {
        ensureOpen();
        return getAdler(strm);
    }
    
    public int getTotalIn() {
        return (int)getBytesRead();
    }
    
    public synchronized long getBytesRead() {
        ensureOpen();
        return getBytesRead(strm);
    }
    
    public int getTotalOut() {
        return (int)getBytesWritten();
    }
    
    public synchronized long getBytesWritten() {
        ensureOpen();
        return getBytesWritten(strm);
    }
    
    public synchronized void reset() {
        ensureOpen();
        reset(strm);
        finished = false;
        needDict = false;
        off = len = 0;
    }
    
    public synchronized void end() {
        if (strm != 0) {
            end(strm);
            strm = 0;
            buf = null;
        }
    }
    
    protected void finalize() {
        end();
    }
    
    private void ensureOpen() {
        if (strm == 0) throw new NullPointerException();
    }
    
    private static native void initIDs();
    
    private static native long init(boolean nowrap);
    
    private static native void setDictionary(long strm, byte[] b, int off, int len);
    
    private native int inflateBytes(byte[] b, int off, int len) throws DataFormatException;
    
    private static native int getAdler(long strm);
    
    private static native long getBytesRead(long strm);
    
    private static native long getBytesWritten(long strm);
    
    private static native void reset(long strm);
    
    private static native void end(long strm);
}
