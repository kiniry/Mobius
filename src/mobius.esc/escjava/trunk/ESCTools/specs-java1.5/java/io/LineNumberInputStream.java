package java.io;


public class LineNumberInputStream extends FilterInputStream {
    int pushBack = -1;
    int lineNumber;
    int markLineNumber;
    int markPushBack = -1;
    
    public LineNumberInputStream(InputStream in) {
        super(in);
    }
    
    public int read() throws IOException {
        int c = pushBack;
        if (c != -1) {
            pushBack = -1;
        } else {
            c = in.read();
        }
        switch (c) {
        case '\r': 
            pushBack = in.read();
            if (pushBack == '\n') {
                pushBack = -1;
            }
        
        case '\n': 
            lineNumber++;
            return '\n';
        
        }
        return c;
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        if (b == null) {
            throw new NullPointerException();
        } else if ((off < 0) || (off > b.length) || (len < 0) || ((off + len) > b.length) || ((off + len) < 0)) {
            throw new IndexOutOfBoundsException();
        } else if (len == 0) {
            return 0;
        }
        int c = read();
        if (c == -1) {
            return -1;
        }
        b[off] = (byte)c;
        int i = 1;
        try {
            for (; i < len; i++) {
                c = read();
                if (c == -1) {
                    break;
                }
                if (b != null) {
                    b[off + i] = (byte)c;
                }
            }
        } catch (IOException ee) {
        }
        return i;
    }
    
    public long skip(long n) throws IOException {
        int chunk = 2048;
        long remaining = n;
        byte[] data;
        int nr;
        if (n <= 0) {
            return 0;
        }
        data = new byte[chunk];
        while (remaining > 0) {
            nr = read(data, 0, (int)Math.min(chunk, remaining));
            if (nr < 0) {
                break;
            }
            remaining -= nr;
        }
        return n - remaining;
    }
    
    public void setLineNumber(int lineNumber) {
        this.lineNumber = lineNumber;
    }
    
    public int getLineNumber() {
        return lineNumber;
    }
    
    public int available() throws IOException {
        return (pushBack == -1) ? super.available() / 2 : super.available() / 2 + 1;
    }
    
    public void mark(int readlimit) {
        markLineNumber = lineNumber;
        markPushBack = pushBack;
        in.mark(readlimit);
    }
    
    public void reset() throws IOException {
        lineNumber = markLineNumber;
        pushBack = markPushBack;
        in.reset();
    }
}
