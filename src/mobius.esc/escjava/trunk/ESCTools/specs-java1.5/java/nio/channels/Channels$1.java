package java.nio.channels;

import java.io.OutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;

class Channels$1 extends OutputStream {
    /*synthetic*/ final WritableByteChannel val$ch;
    
    Channels$1(/*synthetic*/ final WritableByteChannel val$ch) throws IOException {
        this.val$ch = val$ch;
        
    }
    private ByteBuffer bb = null;
    private byte[] bs = null;
    private byte[] b1 = null;
    
    public synchronized void write(int b) throws IOException {
        if (b1 == null) b1 = new byte[1];
        b1[0] = (byte)b;
        this.write(b1);
    }
    
    public synchronized void write(byte[] bs, int off, int len) throws IOException {
        if ((off < 0) || (off > bs.length) || (len < 0) || ((off + len) > bs.length) || ((off + len) < 0)) {
            throw new IndexOutOfBoundsException();
        } else if (len == 0) {
            return;
        }
        ByteBuffer bb = ((this.bs == bs) ? this.bb : ByteBuffer.wrap(bs));
        bb.limit(Math.min(off + len, bb.capacity()));
        bb.position(off);
        this.bb = bb;
        this.bs = bs;
        Channels.access$000(val$ch, bb);
    }
    
    public void close() throws IOException {
        val$ch.close();
    }
}
