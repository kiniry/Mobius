package java.util.jar;

import java.io.FilterInputStream;
import java.io.InputStream;
import java.io.IOException;

class Manifest$FastInputStream extends FilterInputStream {
    private byte[] buf;
    private int count = 0;
    private int pos = 0;
    
    Manifest$FastInputStream(InputStream in) {
        this(in, 8192);
    }
    
    Manifest$FastInputStream(InputStream in, int size) {
        super(in);
        buf = new byte[size];
    }
    
    public int read() throws IOException {
        if (pos >= count) {
            fill();
            if (pos >= count) {
                return -1;
            }
        }
        return buf[pos++] & 255;
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        int avail = count - pos;
        if (avail <= 0) {
            if (len >= buf.length) {
                return in.read(b, off, len);
            }
            fill();
            avail = count - pos;
            if (avail <= 0) {
                return -1;
            }
        }
        if (len > avail) {
            len = avail;
        }
        System.arraycopy(buf, pos, b, off, len);
        pos += len;
        return len;
    }
    
    public int readLine(byte[] b, int off, int len) throws IOException {
        byte[] tbuf = this.buf;
        int total = 0;
        while (total < len) {
            int avail = count - pos;
            if (avail <= 0) {
                fill();
                avail = count - pos;
                if (avail <= 0) {
                    return -1;
                }
            }
            int n = len - total;
            if (n > avail) {
                n = avail;
            }
            int tpos = pos;
            int maxpos = tpos + n;
            while (tpos < maxpos && tbuf[tpos++] != '\n') ;
            n = tpos - pos;
            System.arraycopy(tbuf, pos, b, off, n);
            off += n;
            total += n;
            pos = tpos;
            if (tbuf[tpos - 1] == '\n') {
                break;
            }
        }
        return total;
    }
    
    public byte peek() throws IOException {
        if (pos == count) fill();
        return buf[pos];
    }
    
    public int readLine(byte[] b) throws IOException {
        return readLine(b, 0, b.length);
    }
    
    public long skip(long n) throws IOException {
        if (n <= 0) {
            return 0;
        }
        long avail = count - pos;
        if (avail <= 0) {
            return in.skip(n);
        }
        if (n > avail) {
            n = avail;
        }
        pos += n;
        return n;
    }
    
    public int available() throws IOException {
        return (count - pos) + in.available();
    }
    
    public void close() throws IOException {
        if (in != null) {
            in.close();
            in = null;
            buf = null;
        }
    }
    
    private void fill() throws IOException {
        count = pos = 0;
        int n = in.read(buf, 0, buf.length);
        if (n > 0) {
            count = n;
        }
    }
}
