package java.io;

class ObjectInputStream$PeekInputStream extends InputStream {
    private final InputStream in;
    private int peekb = -1;
    
    ObjectInputStream$PeekInputStream(InputStream in) {
        
        this.in = in;
    }
    
    int peek() throws IOException {
        return (peekb >= 0) ? peekb : (peekb = in.read());
    }
    
    public int read() throws IOException {
        if (peekb >= 0) {
            int v = peekb;
            peekb = -1;
            return v;
        } else {
            return in.read();
        }
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        if (len == 0) {
            return 0;
        } else if (peekb < 0) {
            return in.read(b, off, len);
        } else {
            b[off++] = (byte)peekb;
            len--;
            peekb = -1;
            int n = in.read(b, off, len);
            return (n >= 0) ? (n + 1) : 1;
        }
    }
    
    void readFully(byte[] b, int off, int len) throws IOException {
        int n = 0;
        while (n < len) {
            int count = read(b, off + n, len - n);
            if (count < 0) {
                throw new EOFException();
            }
            n += count;
        }
    }
    
    public long skip(long n) throws IOException {
        if (n <= 0) {
            return 0;
        }
        int skipped = 0;
        if (peekb >= 0) {
            peekb = -1;
            skipped++;
            n--;
        }
        return skipped + skip(n);
    }
    
    public int available() throws IOException {
        return in.available() + ((peekb >= 0) ? 1 : 0);
    }
    
    public void close() throws IOException {
        in.close();
    }
}
