package java.util.zip;

public class Deflater {
    private long strm;
    private byte[] buf = new byte[0];
    private int off;
    private int len;
    private int level;
    private int strategy;
    private boolean setParams;
    private boolean finish;
    private boolean finished;
    public static final int DEFLATED = 8;
    public static final int NO_COMPRESSION = 0;
    public static final int BEST_SPEED = 1;
    public static final int BEST_COMPRESSION = 9;
    public static final int DEFAULT_COMPRESSION = -1;
    public static final int FILTERED = 1;
    public static final int HUFFMAN_ONLY = 2;
    public static final int DEFAULT_STRATEGY = 0;
    static {
        initIDs();
    }
    
    public Deflater(int level, boolean nowrap) {
        
        this.level = level;
        this.strategy = DEFAULT_STRATEGY;
        strm = init(level, DEFAULT_STRATEGY, nowrap);
    }
    
    public Deflater(int level) {
        this(level, false);
    }
    
    public Deflater() {
        this(DEFAULT_COMPRESSION, false);
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
    }
    
    public void setDictionary(byte[] b) {
        setDictionary(b, 0, b.length);
    }
    
    public synchronized void setStrategy(int strategy) {
        switch (strategy) {
        case DEFAULT_STRATEGY: 
        
        case FILTERED: 
        
        case HUFFMAN_ONLY: 
            break;
        
        default: 
            throw new IllegalArgumentException();
        
        }
        if (this.strategy != strategy) {
            this.strategy = strategy;
            setParams = true;
        }
    }
    
    public synchronized void setLevel(int level) {
        if ((level < 0 || level > 9) && level != DEFAULT_COMPRESSION) {
            throw new IllegalArgumentException("invalid compression level");
        }
        if (this.level != level) {
            this.level = level;
            setParams = true;
        }
    }
    
    public boolean needsInput() {
        return len <= 0;
    }
    
    public synchronized void finish() {
        finish = true;
    }
    
    public synchronized boolean finished() {
        return finished;
    }
    
    public synchronized int deflate(byte[] b, int off, int len) {
        if (b == null) {
            throw new NullPointerException();
        }
        if (off < 0 || len < 0 || off > b.length - len) {
            throw new ArrayIndexOutOfBoundsException();
        }
        return deflateBytes(b, off, len);
    }
    
    public int deflate(byte[] b) {
        return deflate(b, 0, b.length);
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
        finish = false;
        finished = false;
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
    
    private static native long init(int level, int strategy, boolean nowrap);
    
    private static native void setDictionary(long strm, byte[] b, int off, int len);
    
    private native int deflateBytes(byte[] b, int off, int len);
    
    private static native int getAdler(long strm);
    
    private static native long getBytesRead(long strm);
    
    private static native long getBytesWritten(long strm);
    
    private static native void reset(long strm);
    
    private static native void end(long strm);
}
