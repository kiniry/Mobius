package java.io;

import java.io.InputStream;
import java.util.Enumeration;
import java.util.Vector;

public class SequenceInputStream extends InputStream {
    Enumeration e;
    InputStream in;
    
    public SequenceInputStream(Enumeration e) {
        
        this.e = e;
        try {
            nextStream();
        } catch (IOException ex) {
            throw new Error("panic");
        }
    }
    
    public SequenceInputStream(InputStream s1, InputStream s2) {
        
        Vector v = new Vector(2);
        v.addElement(s1);
        v.addElement(s2);
        e = v.elements();
        try {
            nextStream();
        } catch (IOException ex) {
            throw new Error("panic");
        }
    }
    
    final void nextStream() throws IOException {
        if (in != null) {
            in.close();
        }
        if (e.hasMoreElements()) {
            in = (InputStream)(InputStream)e.nextElement();
            if (in == null) throw new NullPointerException();
        } else in = null;
    }
    
    public int available() throws IOException {
        if (in == null) {
            return 0;
        }
        return in.available();
    }
    
    public int read() throws IOException {
        if (in == null) {
            return -1;
        }
        int c = in.read();
        if (c == -1) {
            nextStream();
            return read();
        }
        return c;
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        if (in == null) {
            return -1;
        } else if (b == null) {
            throw new NullPointerException();
        } else if ((off < 0) || (off > b.length) || (len < 0) || ((off + len) > b.length) || ((off + len) < 0)) {
            throw new IndexOutOfBoundsException();
        } else if (len == 0) {
            return 0;
        }
        int n = in.read(b, off, len);
        if (n <= 0) {
            nextStream();
            return read(b, off, len);
        }
        return n;
    }
    
    public void close() throws IOException {
        do {
            nextStream();
        }         while (in != null);
    }
}
