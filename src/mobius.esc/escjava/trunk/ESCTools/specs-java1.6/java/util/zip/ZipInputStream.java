package java.util.zip;

import java.io.InputStream;
import java.io.IOException;
import java.io.EOFException;
import java.io.PushbackInputStream;

public class ZipInputStream extends InflaterInputStream implements ZipConstants {
    private ZipEntry entry;
    private CRC32 crc = new CRC32();
    private long remaining;
    private byte[] tmpbuf = new byte[512];
    private static final int STORED = ZipEntry.STORED;
    private static final int DEFLATED = ZipEntry.DEFLATED;
    private boolean closed = false;
    private boolean entryEOF = false;
    
    private void ensureOpen() throws IOException {
        if (closed) {
            throw new IOException("Stream closed");
        }
    }
    
    public ZipInputStream(InputStream in) {
        super(new PushbackInputStream(in, 512), new Inflater(true), 512);
        usesDefaultInflater = true;
        if (in == null) {
            throw new NullPointerException("in is null");
        }
    }
    
    public ZipEntry getNextEntry() throws IOException {
        ensureOpen();
        if (entry != null) {
            closeEntry();
        }
        crc.reset();
        inf.reset();
        if ((entry = readLOC()) == null) {
            return null;
        }
        if (entry.method == STORED) {
            remaining = entry.size;
        }
        entryEOF = false;
        return entry;
    }
    
    public void closeEntry() throws IOException {
        ensureOpen();
        while (read(tmpbuf, 0, tmpbuf.length) != -1) ;
        entryEOF = true;
    }
    
    public int available() throws IOException {
        ensureOpen();
        if (entryEOF) {
            return 0;
        } else {
            return 1;
        }
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        ensureOpen();
        if (off < 0 || len < 0 || off > b.length - len) {
            throw new IndexOutOfBoundsException();
        } else if (len == 0) {
            return 0;
        }
        if (entry == null) {
            return -1;
        }
        switch (entry.method) {
        case DEFLATED: 
            len = super.read(b, off, len);
            if (len == -1) {
                readEnd(entry);
                entryEOF = true;
                entry = null;
            } else {
                crc.update(b, off, len);
            }
            return len;
        
        case STORED: 
            if (remaining <= 0) {
                entryEOF = true;
                entry = null;
                return -1;
            }
            if (len > remaining) {
                len = (int)remaining;
            }
            len = in.read(b, off, len);
            if (len == -1) {
                throw new ZipException("unexpected EOF");
            }
            crc.update(b, off, len);
            remaining -= len;
            if (remaining == 0 && entry.crc != crc.getValue()) {
                throw new ZipException("invalid entry CRC (expected 0x" + Long.toHexString(entry.crc) + " but got 0x" + Long.toHexString(crc.getValue()) + ")");
            }
            return len;
        
        default: 
            throw new InternalError("invalid compression method");
        
        }
    }
    
    public long skip(long n) throws IOException {
        if (n < 0) {
            throw new IllegalArgumentException("negative skip length");
        }
        ensureOpen();
        int max = (int)Math.min(n, Integer.MAX_VALUE);
        int total = 0;
        while (total < max) {
            int len = max - total;
            if (len > tmpbuf.length) {
                len = tmpbuf.length;
            }
            len = read(tmpbuf, 0, len);
            if (len == -1) {
                entryEOF = true;
                break;
            }
            total += len;
        }
        return total;
    }
    
    public void close() throws IOException {
        if (!closed) {
            super.close();
            closed = true;
        }
    }
    private byte[] b = new byte[256];
    
    private ZipEntry readLOC() throws IOException {
        try {
            readFully(tmpbuf, 0, LOCHDR);
        } catch (EOFException e) {
            return null;
        }
        if (get32(tmpbuf, 0) != LOCSIG) {
            return null;
        }
        int len = get16(tmpbuf, LOCNAM);
        if (len == 0) {
            throw new ZipException("missing entry name");
        }
        int blen = b.length;
        if (len > blen) {
            do blen = blen * 2;             while (len > blen);
            b = new byte[blen];
        }
        readFully(b, 0, len);
        ZipEntry e = createZipEntry(getUTF8String(b, 0, len));
        e.version = get16(tmpbuf, LOCVER);
        e.flag = get16(tmpbuf, LOCFLG);
        if ((e.flag & 1) == 1) {
            throw new ZipException("encrypted ZIP entry not supported");
        }
        e.method = get16(tmpbuf, LOCHOW);
        e.time = get32(tmpbuf, LOCTIM);
        if ((e.flag & 8) == 8) {
            if (e.method != DEFLATED) {
                throw new ZipException("only DEFLATED entries can have EXT descriptor");
            }
        } else {
            e.crc = get32(tmpbuf, LOCCRC);
            e.csize = get32(tmpbuf, LOCSIZ);
            e.size = get32(tmpbuf, LOCLEN);
        }
        len = get16(tmpbuf, LOCEXT);
        if (len > 0) {
            byte[] bb = new byte[len];
            readFully(bb, 0, len);
            e.extra = bb;
        }
        return e;
    }
    
    private static String getUTF8String(byte[] b, int off, int len) {
        int count = 0;
        int max = off + len;
        int i = off;
        while (i < max) {
            int c = b[i++] & 255;
            switch (c >> 4) {
            case 0: 
            
            case 1: 
            
            case 2: 
            
            case 3: 
            
            case 4: 
            
            case 5: 
            
            case 6: 
            
            case 7: 
                count++;
                break;
            
            case 12: 
            
            case 13: 
                if ((int)(b[i++] & 192) != 128) {
                    throw new IllegalArgumentException();
                }
                count++;
                break;
            
            case 14: 
                if (((int)(b[i++] & 192) != 128) || ((int)(b[i++] & 192) != 128)) {
                    throw new IllegalArgumentException();
                }
                count++;
                break;
            
            default: 
                throw new IllegalArgumentException();
            
            }
        }
        if (i != max) {
            throw new IllegalArgumentException();
        }
        char[] cs = new char[count];
        i = 0;
        while (off < max) {
            int c = b[off++] & 255;
            switch (c >> 4) {
            case 0: 
            
            case 1: 
            
            case 2: 
            
            case 3: 
            
            case 4: 
            
            case 5: 
            
            case 6: 
            
            case 7: 
                cs[i++] = (char)c;
                break;
            
            case 12: 
            
            case 13: 
                cs[i++] = (char)(((c & 31) << 6) | (b[off++] & 63));
                break;
            
            case 14: 
                int t = (b[off++] & 63) << 6;
                cs[i++] = (char)(((c & 15) << 12) | t | (b[off++] & 63));
                break;
            
            default: 
                throw new IllegalArgumentException();
            
            }
        }
        return new String(cs, 0, count);
    }
    
    protected ZipEntry createZipEntry(String name) {
        return new ZipEntry(name);
    }
    
    private void readEnd(ZipEntry e) throws IOException {
        int n = inf.getRemaining();
        if (n > 0) {
            ((PushbackInputStream)(PushbackInputStream)in).unread(buf, len - n, n);
        }
        if ((e.flag & 8) == 8) {
            readFully(tmpbuf, 0, EXTHDR);
            long sig = get32(tmpbuf, 0);
            if (sig != EXTSIG) {
                e.crc = sig;
                e.csize = get32(tmpbuf, EXTSIZ - EXTCRC);
                e.size = get32(tmpbuf, EXTLEN - EXTCRC);
                ((PushbackInputStream)(PushbackInputStream)in).unread(tmpbuf, EXTHDR - EXTCRC - 1, EXTCRC);
            } else {
                e.crc = get32(tmpbuf, EXTCRC);
                e.csize = get32(tmpbuf, EXTSIZ);
                e.size = get32(tmpbuf, EXTLEN);
            }
        }
        if (e.size != inf.getBytesWritten()) {
            throw new ZipException("invalid entry size (expected " + e.size + " but got " + inf.getBytesWritten() + " bytes)");
        }
        if (e.csize != inf.getBytesRead()) {
            throw new ZipException("invalid entry compressed size (expected " + e.csize + " but got " + inf.getBytesRead() + " bytes)");
        }
        if (e.crc != crc.getValue()) {
            throw new ZipException("invalid entry CRC (expected 0x" + Long.toHexString(e.crc) + " but got 0x" + Long.toHexString(crc.getValue()) + ")");
        }
    }
    
    private void readFully(byte[] b, int off, int len) throws IOException {
        while (len > 0) {
            int n = in.read(b, off, len);
            if (n == -1) {
                throw new EOFException();
            }
            off += n;
            len -= n;
        }
    }
    
    private static final int get16(byte[] b, int off) {
        return (b[off] & 255) | ((b[off + 1] & 255) << 8);
    }
    
    private static final long get32(byte[] b, int off) {
        return get16(b, off) | ((long)get16(b, off + 2) << 16);
    }
}
