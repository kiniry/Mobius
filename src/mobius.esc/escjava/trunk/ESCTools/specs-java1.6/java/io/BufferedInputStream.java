package java.io;

import java.util.concurrent.atomic.AtomicReferenceFieldUpdater;

public class BufferedInputStream extends FilterInputStream {
    private static int defaultBufferSize = 8192;
    protected volatile byte[] buf;
    private static final AtomicReferenceFieldUpdater bufUpdater = AtomicReferenceFieldUpdater.newUpdater(BufferedInputStream.class, byte[].class, "buf");
    protected int count;
    protected int pos;
    protected int markpos = -1;
    protected int marklimit;
    
    private InputStream getInIfOpen() throws IOException {
        InputStream input = in;
        if (input == null) throw new IOException("Stream closed");
        return input;
    }
    
    private byte[] getBufIfOpen() throws IOException {
        byte[] buffer = buf;
        if (buffer == null) throw new IOException("Stream closed");
        return buffer;
    }
    
    public BufferedInputStream(InputStream in) {
        this(in, defaultBufferSize);
    }
    
    public BufferedInputStream(InputStream in, int size) {
        super(in);
        if (size <= 0) {
            throw new IllegalArgumentException("Buffer size <= 0");
        }
        buf = new byte[size];
    }
    
    private void fill() throws IOException {
        byte[] buffer = getBufIfOpen();
        if (markpos < 0) pos = 0; else if (pos >= buffer.length) if (markpos > 0) {
            int sz = pos - markpos;
            System.arraycopy(buffer, markpos, buffer, 0, sz);
            pos = sz;
            markpos = 0;
        } else if (buffer.length >= marklimit) {
            markpos = -1;
            pos = 0;
        } else {
            int nsz = pos * 2;
            if (nsz > marklimit) nsz = marklimit;
            byte[] nbuf = new byte[nsz];
            System.arraycopy(buffer, 0, nbuf, 0, pos);
            if (!bufUpdater.compareAndSet(this, buffer, nbuf)) {
                throw new IOException("Stream closed");
            }
            buffer = nbuf;
        }
        count = pos;
        int n = getInIfOpen().read(buffer, pos, buffer.length - pos);
        if (n > 0) count = n + pos;
    }
    
    public synchronized int read() throws IOException {
        if (pos >= count) {
            fill();
            if (pos >= count) return -1;
        }
        return getBufIfOpen()[pos++] & 255;
    }
    
    private int read1(byte[] b, int off, int len) throws IOException {
        int avail = count - pos;
        if (avail <= 0) {
            if (len >= getBufIfOpen().length && markpos < 0) {
                return getInIfOpen().read(b, off, len);
            }
            fill();
            avail = count - pos;
            if (avail <= 0) return -1;
        }
        int cnt = (avail < len) ? avail : len;
        System.arraycopy(getBufIfOpen(), pos, b, off, cnt);
        pos += cnt;
        return cnt;
    }
    
    public synchronized int read(byte[] b, int off, int len) throws IOException {
        getBufIfOpen();
        if ((off | len | (off + len) | (b.length - (off + len))) < 0) {
            throw new IndexOutOfBoundsException();
        } else if (len == 0) {
            return 0;
        }
        int n = 0;
        for (; ; ) {
            int nread = read1(b, off + n, len - n);
            if (nread <= 0) return (n == 0) ? nread : n;
            n += nread;
            if (n >= len) return n;
            InputStream input = in;
            if (input != null && input.available() <= 0) return n;
        }
    }
    
    public synchronized long skip(long n) throws IOException {
        getBufIfOpen();
        if (n <= 0) {
            return 0;
        }
        long avail = count - pos;
        if (avail <= 0) {
            if (markpos < 0) return getInIfOpen().skip(n);
            fill();
            avail = count - pos;
            if (avail <= 0) return 0;
        }
        long skipped = (avail < n) ? avail : n;
        pos += skipped;
        return skipped;
    }
    
    public synchronized int available() throws IOException {
        return getInIfOpen().available() + (count - pos);
    }
    
    public synchronized void mark(int readlimit) {
        marklimit = readlimit;
        markpos = pos;
    }
    
    public synchronized void reset() throws IOException {
        getBufIfOpen();
        if (markpos < 0) throw new IOException("Resetting to invalid mark");
        pos = markpos;
    }
    
    public boolean markSupported() {
        return true;
    }
    
    public void close() throws IOException {
        byte[] buffer;
        while ((buffer = buf) != null) {
            if (bufUpdater.compareAndSet(this, buffer, null)) {
                InputStream input = in;
                in = null;
                if (input != null) input.close();
                return;
            }
        }
    }
}
