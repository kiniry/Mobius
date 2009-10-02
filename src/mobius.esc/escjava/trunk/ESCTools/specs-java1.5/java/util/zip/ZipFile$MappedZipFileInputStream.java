package java.util.zip;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.MappedByteBuffer;
import sun.nio.ByteBuffered;
import java.lang.reflect.*;

class ZipFile$MappedZipFileInputStream extends ZipFile$ZipFileInputStream implements ByteBuffered {
    /*synthetic*/ final ZipFile this$0;
    private ByteBuffer directBuffer = null;
    private String name;
    
    ZipFile$MappedZipFileInputStream(/*synthetic*/ final ZipFile this$0, long jzentry, String name) {
        super(this$0, jzentry);
        this.this$0 = this$0;
	this.name = name;
        int offset = (int)ZipFile.access$1600(jzentry);
        MappedByteBuffer bb = ZipFile.access$1700(this$0);
        synchronized (bb) {
            bb.position(offset);
            bb.limit((int)(offset + rem));
            this.directBuffer = bb.slice();
            bb.position(0);
            bb.limit(bb.capacity());
        }
    }
    
    public ByteBuffer getByteBuffer() throws IOException {
        synchronized (this$0) {
            ZipFile.access$1400(this$0);
            ZipFile.access$1802(this$0, true);
            return directBuffer;
        }
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        int rem = directBuffer.remaining();
        if (rem == 0) {
            return -1;
        }
        if (len <= 0) {
            return 0;
        }
        if (len > rem) {
            len = rem;
        }
        synchronized (this$0) {
            ZipFile.access$1400(this$0);
            directBuffer.get(b, off, len);
        }
        if (len == rem) {
            close();
        }
        return len;
    }
    
    public int read() throws IOException {
        synchronized (this$0) {
            ZipFile.access$1400(this$0);
            if (directBuffer.remaining() == 0) {
                return -1;
            } else {
                return directBuffer.get() & 255;
            }
        }
    }
    
    public long skip(long n) {
        int rem = directBuffer.remaining();
        int len = n > rem ? rem : (int)n;
        directBuffer.position(directBuffer.position() + len);
        if (len == rem) {
            close();
        }
        return len;
    }
    
    public int available() {
        return directBuffer.remaining();
    }
    
    public long size() {
        return size;
    }
    
    public void close() {
        directBuffer.position(directBuffer.limit());
        synchronized (this$0) {
            if (jzentry != 0 && ZipFile.access$600(this$0) != 0) {
                ZipFile.access$1100(ZipFile.access$600(this$0), jzentry);
                jzentry = 0;
            }
        }
    }
}
