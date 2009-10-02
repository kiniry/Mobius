package java.util.zip;

import java.io.IOException;
import java.io.EOFException;
import java.lang.reflect.*;

class ZipFile$2 extends InflaterInputStream {
    /*synthetic*/ final ZipFile this$0;
    /*synthetic*/ final ZipFile$ZipFileInputStream val$zfin;
    
    ZipFile$2(/*synthetic*/ final ZipFile this$0, java.io.InputStream x0, java.util.zip.Inflater x1, int x2, /*synthetic*/ final ZipFile$ZipFileInputStream val$zfin) throws IOException {
        super(x0, x1, x2);
	this.this$0 = this$0;
        this.val$zfin = val$zfin;
    }
    private boolean isClosed = false;
    
    public void close() throws IOException {
        if (!isClosed) {
            ZipFile.access$300(this$0, inf);
            this.in.close();
            isClosed = true;
        }
    }
    
    protected void fill() throws IOException {
        if (eof) {
            throw new EOFException("Unexpected end of ZLIB input stream");
        }
        len = this.in.read(buf, 0, buf.length);
        if (len == -1) {
            buf[0] = 0;
            len = 1;
            eof = true;
        }
        inf.setInput(buf, 0, len);
    }
    private boolean eof;
    
    public int available() throws IOException {
        if (isClosed) return 0;
        long avail = val$zfin.size() - inf.getBytesWritten();
        return avail > (long)Integer.MAX_VALUE ? Integer.MAX_VALUE : (int)avail;
    }
}
