package java.util.zip;

import java.io.OutputStream;
import java.io.IOException;

public class GZIPOutputStream extends DeflaterOutputStream {
    protected CRC32 crc = new CRC32();
    private static final int GZIP_MAGIC = 35615;
    private static final int TRAILER_SIZE = 8;
    
    public GZIPOutputStream(OutputStream out, int size) throws IOException {
        super(out, new Deflater(Deflater.DEFAULT_COMPRESSION, true), size);
        usesDefaultDeflater = true;
        writeHeader();
        crc.reset();
    }
    
    public GZIPOutputStream(OutputStream out) throws IOException {
        this(out, 512);
    }
    
    public synchronized void write(byte[] buf, int off, int len) throws IOException {
        super.write(buf, off, len);
        crc.update(buf, off, len);
    }
    
    public void finish() throws IOException {
        if (!def.finished()) {
            def.finish();
            while (!def.finished()) {
                int len = def.deflate(buf, 0, buf.length);
                if (def.finished() && len <= buf.length - TRAILER_SIZE) {
                    writeTrailer(buf, len);
                    len = len + TRAILER_SIZE;
                    out.write(buf, 0, len);
                    return;
                }
                if (len > 0) out.write(buf, 0, len);
            }
            byte[] trailer = new byte[TRAILER_SIZE];
            writeTrailer(trailer, 0);
            out.write(trailer);
        }
    }
    private static final byte[] header = {(byte)GZIP_MAGIC, (byte)(GZIP_MAGIC >> 8), Deflater.DEFLATED, 0, 0, 0, 0, 0, 0, 0};
    
    private void writeHeader() throws IOException {
        out.write(header);
    }
    
    private void writeTrailer(byte[] buf, int offset) throws IOException {
        writeInt((int)crc.getValue(), buf, offset);
        writeInt(def.getTotalIn(), buf, offset + 4);
    }
    
    private void writeInt(int i, byte[] buf, int offset) throws IOException {
        writeShort(i & 65535, buf, offset);
        writeShort((i >> 16) & 65535, buf, offset + 2);
    }
    
    private void writeShort(int s, byte[] buf, int offset) throws IOException {
        buf[offset] = (byte)(s & 255);
        buf[offset + 1] = (byte)((s >> 8) & 255);
    }
}
