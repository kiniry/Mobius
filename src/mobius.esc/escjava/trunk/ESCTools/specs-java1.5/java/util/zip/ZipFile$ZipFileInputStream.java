package java.util.zip;

import java.io.InputStream;
import java.io.IOException;
import java.lang.reflect.*;

class ZipFile$ZipFileInputStream extends InputStream {
    /*synthetic*/ final ZipFile this$0;
    protected long jzentry;
    private long pos;
    protected long rem;
    protected long size;
    
    ZipFile$ZipFileInputStream(/*synthetic*/ final ZipFile this$0, long jzentry) {
        this.this$0 = this$0;
        
        pos = 0;
        rem = ZipFile.access$1200(jzentry);
        size = ZipFile.access$1300(jzentry);
        this.jzentry = jzentry;
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        if (rem == 0) {
            return -1;
        }
        if (len <= 0) {
            return 0;
        }
        if (len > rem) {
            len = (int)rem;
        }
        synchronized (this$0) {
            ZipFile.access$1400(this$0);
            len = ZipFile.access$1500(ZipFile.access$600(this$0), jzentry, pos, b, off, len);
        }
        if (len > 0) {
            pos += len;
            rem -= len;
        }
        if (rem == 0) {
            close();
        }
        return len;
    }
    
    public int read() throws IOException {
        byte[] b = new byte[1];
        if (read(b, 0, 1) == 1) {
            return b[0] & 255;
        } else {
            return -1;
        }
    }
    
    public long skip(long n) {
        if (n > rem) n = rem;
        pos += n;
        rem -= n;
        if (rem == 0) {
            close();
        }
        return n;
    }
    
    public int available() {
        return rem > Integer.MAX_VALUE ? Integer.MAX_VALUE : (int)rem;
    }
    
    public long size() {
        return size;
    }
    
    public void close() {
        rem = 0;
        synchronized (this$0) {
            if (jzentry != 0 && ZipFile.access$600(this$0) != 0) {
                ZipFile.access$1100(ZipFile.access$600(this$0), jzentry);
                jzentry = 0;
            }
        }
    }
}
