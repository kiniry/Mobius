package java.io;

public class LineNumberReader extends BufferedReader {
    private int lineNumber = 0;
    private int markedLineNumber;
    private boolean skipLF;
    private boolean markedSkipLF;
    
    public LineNumberReader(Reader in) {
        super(in);
    }
    
    public LineNumberReader(Reader in, int sz) {
        super(in, sz);
    }
    
    public void setLineNumber(int lineNumber) {
        this.lineNumber = lineNumber;
    }
    
    public int getLineNumber() {
        return lineNumber;
    }
    
    public int read() throws IOException {
        synchronized (lock) {
            int c = super.read();
            if (skipLF) {
                if (c == '\n') c = super.read();
                skipLF = false;
            }
            switch (c) {
            case '\r': 
                skipLF = true;
            
            case '\n': 
                lineNumber++;
                return '\n';
            
            }
            return c;
        }
    }
    
    public int read(char[] cbuf, int off, int len) throws IOException {
        synchronized (lock) {
            int n = super.read(cbuf, off, len);
            for (int i = off; i < off + n; i++) {
                int c = cbuf[i];
                if (skipLF) {
                    skipLF = false;
                    if (c == '\n') continue;
                }
                switch (c) {
                case '\r': 
                    skipLF = true;
                
                case '\n': 
                    lineNumber++;
                    break;
                
                }
            }
            return n;
        }
    }
    
    public String readLine() throws IOException {
        synchronized (lock) {
            String l = super.readLine(skipLF);
            skipLF = false;
            if (l != null) lineNumber++;
            return l;
        }
    }
    private static final int maxSkipBufferSize = 8192;
    private char[] skipBuffer = null;
    
    public long skip(long n) throws IOException {
        if (n < 0) throw new IllegalArgumentException("skip() value is negative");
        int nn = (int)Math.min(n, maxSkipBufferSize);
        synchronized (lock) {
            if ((skipBuffer == null) || (skipBuffer.length < nn)) skipBuffer = new char[nn];
            long r = n;
            while (r > 0) {
                int nc = read(skipBuffer, 0, (int)Math.min(r, nn));
                if (nc == -1) break;
                r -= nc;
            }
            return n - r;
        }
    }
    
    public void mark(int readAheadLimit) throws IOException {
        synchronized (lock) {
            super.mark(readAheadLimit);
            markedLineNumber = lineNumber;
            markedSkipLF = skipLF;
        }
    }
    
    public void reset() throws IOException {
        synchronized (lock) {
            super.reset();
            lineNumber = markedLineNumber;
            skipLF = markedSkipLF;
        }
    }
}
