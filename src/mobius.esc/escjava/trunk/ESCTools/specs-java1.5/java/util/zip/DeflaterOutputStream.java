package java.util.zip;

import java.io.FilterOutputStream;
import java.io.OutputStream;
import java.io.IOException;

public class DeflaterOutputStream extends FilterOutputStream {
    protected Deflater def;
    protected byte[] buf;
    private boolean closed = false;
    
    public DeflaterOutputStream(OutputStream out, Deflater def, int size) {
        super(out);
        if (out == null || def == null) {
            throw new NullPointerException();
        } else if (size <= 0) {
            throw new IllegalArgumentException("buffer size <= 0");
        }
        this.def = def;
        buf = new byte[size];
    }
    
    public DeflaterOutputStream(OutputStream out, Deflater def) {
        this(out, def, 512);
    }
    boolean usesDefaultDeflater = false;
    
    public DeflaterOutputStream(OutputStream out) {
        this(out, new Deflater());
        usesDefaultDeflater = true;
    }
    
    public void write(int b) throws IOException {
        byte[] buf = new byte[1];
        buf[0] = (byte)(b & 255);
        write(buf, 0, 1);
    }
    
    public void write(byte[] b, int off, int len) throws IOException {
        if (def.finished()) {
            throw new IOException("write beyond end of stream");
        }
        if ((off | len | (off + len) | (b.length - (off + len))) < 0) {
            throw new IndexOutOfBoundsException();
        } else if (len == 0) {
            return;
        }
        if (!def.finished()) {
            int stride = buf.length;
            for (int i = 0; i < len; i += stride) {
                def.setInput(b, off + i, Math.min(stride, len - i));
                while (!def.needsInput()) {
                    deflate();
                }
            }
        }
    }
    
    public void finish() throws IOException {
        if (!def.finished()) {
            def.finish();
            while (!def.finished()) {
                deflate();
            }
        }
    }
    
    public void close() throws IOException {
        if (!closed) {
            finish();
            if (usesDefaultDeflater) def.end();
            out.close();
            closed = true;
        }
    }
    
    protected void deflate() throws IOException {
        int len = def.deflate(buf, 0, buf.length);
        if (len > 0) {
            out.write(buf, 0, len);
        }
    }
}
