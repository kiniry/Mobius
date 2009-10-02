package java.io;

public class BufferedWriter extends Writer {
    private Writer out;
    private char[] cb;
    private int nChars;
    private int nextChar;
    private static int defaultCharBufferSize = 8192;
    private String lineSeparator;
    
    public BufferedWriter(Writer out) {
        this(out, defaultCharBufferSize);
    }
    
    public BufferedWriter(Writer out, int sz) {
        super(out);
        if (sz <= 0) throw new IllegalArgumentException("Buffer size <= 0");
        this.out = out;
        cb = new char[sz];
        nChars = sz;
        nextChar = 0;
        lineSeparator = (String)(String)java.security.AccessController.doPrivileged(new sun.security.action.GetPropertyAction("line.separator"));
    }
    
    private void ensureOpen() throws IOException {
        if (out == null) throw new IOException("Stream closed");
    }
    
    void flushBuffer() throws IOException {
        synchronized (lock) {
            ensureOpen();
            if (nextChar == 0) return;
            out.write(cb, 0, nextChar);
            nextChar = 0;
        }
    }
    
    public void write(int c) throws IOException {
        synchronized (lock) {
            ensureOpen();
            if (nextChar >= nChars) flushBuffer();
            cb[nextChar++] = (char)c;
        }
    }
    
    private int min(int a, int b) {
        if (a < b) return a;
        return b;
    }
    
    public void write(char[] cbuf, int off, int len) throws IOException {
        synchronized (lock) {
            ensureOpen();
            if ((off < 0) || (off > cbuf.length) || (len < 0) || ((off + len) > cbuf.length) || ((off + len) < 0)) {
                throw new IndexOutOfBoundsException();
            } else if (len == 0) {
                return;
            }
            if (len >= nChars) {
                flushBuffer();
                out.write(cbuf, off, len);
                return;
            }
            int b = off;
            int t = off + len;
            while (b < t) {
                int d = min(nChars - nextChar, t - b);
                System.arraycopy(cbuf, b, cb, nextChar, d);
                b += d;
                nextChar += d;
                if (nextChar >= nChars) flushBuffer();
            }
        }
    }
    
    public void write(String s, int off, int len) throws IOException {
        synchronized (lock) {
            ensureOpen();
            int b = off;
            int t = off + len;
            while (b < t) {
                int d = min(nChars - nextChar, t - b);
                s.getChars(b, b + d, cb, nextChar);
                b += d;
                nextChar += d;
                if (nextChar >= nChars) flushBuffer();
            }
        }
    }
    
    public void newLine() throws IOException {
        write(lineSeparator);
    }
    
    public void flush() throws IOException {
        synchronized (lock) {
            flushBuffer();
            out.flush();
        }
    }
    
    public void close() throws IOException {
        synchronized (lock) {
            if (out == null) return;
            flushBuffer();
            out.close();
            out = null;
            cb = null;
        }
    }
}
