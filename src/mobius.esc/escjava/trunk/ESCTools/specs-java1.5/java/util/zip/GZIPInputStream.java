package java.util.zip;

import java.io.SequenceInputStream;
import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.io.IOException;
import java.io.EOFException;

public class GZIPInputStream extends InflaterInputStream {
    protected CRC32 crc = new CRC32();
    protected boolean eos;
    private boolean closed = false;
    
    private void ensureOpen() throws IOException {
        if (closed) {
            throw new IOException("Stream closed");
        }
    }
    
    public GZIPInputStream(InputStream in, int size) throws IOException {
        super(in, new Inflater(true), size);
        usesDefaultInflater = true;
        readHeader();
        crc.reset();
    }
    
    public GZIPInputStream(InputStream in) throws IOException {
        this(in, 512);
    }
    
    public int read(byte[] buf, int off, int len) throws IOException {
        ensureOpen();
        if (eos) {
            return -1;
        }
        len = super.read(buf, off, len);
        if (len == -1) {
            readTrailer();
            eos = true;
        } else {
            crc.update(buf, off, len);
        }
        return len;
    }
    
    public void close() throws IOException {
        if (!closed) {
            super.close();
            eos = true;
            closed = true;
        }
    }
    public static final int GZIP_MAGIC = 35615;
    private static final int FTEXT = 1;
    private static final int FHCRC = 2;
    private static final int FEXTRA = 4;
    private static final int FNAME = 8;
    private static final int FCOMMENT = 16;
    
    private void readHeader() throws IOException {
        CheckedInputStream in = new CheckedInputStream(this.in, crc);
        crc.reset();
        if (readUShort(in) != GZIP_MAGIC) {
            throw new IOException("Not in GZIP format");
        }
        if (readUByte(in) != 8) {
            throw new IOException("Unsupported compression method");
        }
        int flg = readUByte(in);
        skipBytes(in, 6);
        if ((flg & FEXTRA) == FEXTRA) {
            skipBytes(in, readUShort(in));
        }
        if ((flg & FNAME) == FNAME) {
            while (readUByte(in) != 0) ;
        }
        if ((flg & FCOMMENT) == FCOMMENT) {
            while (readUByte(in) != 0) ;
        }
        if ((flg & FHCRC) == FHCRC) {
            int v = (int)crc.getValue() & 65535;
            if (readUShort(in) != v) {
                throw new IOException("Corrupt GZIP header");
            }
        }
    }
    
    private void readTrailer() throws IOException {
        InputStream in = this.in;
        int n = inf.getRemaining();
        if (n > 0) {
            in = new SequenceInputStream(new ByteArrayInputStream(buf, len - n, n), in);
        }
        if ((readUInt(in) != crc.getValue()) || (readUInt(in) != (inf.getBytesWritten() & 4294967295L))) throw new IOException("Corrupt GZIP trailer");
    }
    
    private long readUInt(InputStream in) throws IOException {
        long s = readUShort(in);
        return ((long)readUShort(in) << 16) | s;
    }
    
    private int readUShort(InputStream in) throws IOException {
        int b = readUByte(in);
        return ((int)readUByte(in) << 8) | b;
    }
    
    private int readUByte(InputStream in) throws IOException {
        int b = in.read();
        if (b == -1) {
            throw new EOFException();
        }
        return b;
    }
    private byte[] tmpbuf = new byte[128];
    
    private void skipBytes(InputStream in, int n) throws IOException {
        while (n > 0) {
            int len = in.read(tmpbuf, 0, n < tmpbuf.length ? n : tmpbuf.length);
            if (len == -1) {
                throw new EOFException();
            }
            n -= len;
        }
    }
}
