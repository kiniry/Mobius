package java.util.zip;

import java.io.OutputStream;
import java.io.IOException;
import java.util.Vector;
import java.util.Hashtable;
import java.util.Enumeration;

public class ZipOutputStream extends DeflaterOutputStream implements ZipConstants {
    private ZipEntry entry;
    private Vector entries = new Vector();
    private Hashtable names = new Hashtable();
    private CRC32 crc = new CRC32();
    private long written = 0;
    private long locoff = 0;
    private String comment;
    private int method = DEFLATED;
    private boolean finished;
    private boolean closed = false;
    
    private void ensureOpen() throws IOException {
        if (closed) {
            throw new IOException("Stream closed");
        }
    }
    public static final int STORED = ZipEntry.STORED;
    public static final int DEFLATED = ZipEntry.DEFLATED;
    
    public ZipOutputStream(OutputStream out) {
        super(out, new Deflater(Deflater.DEFAULT_COMPRESSION, true));
        usesDefaultDeflater = true;
    }
    
    public void setComment(String comment) {
        if (comment != null && comment.length() > 65535 / 3 && getUTF8Length(comment) > 65535) {
            throw new IllegalArgumentException("ZIP file comment too long.");
        }
        this.comment = comment;
    }
    
    public void setMethod(int method) {
        if (method != DEFLATED && method != STORED) {
            throw new IllegalArgumentException("invalid compression method");
        }
        this.method = method;
    }
    
    public void setLevel(int level) {
        def.setLevel(level);
    }
    
    public void putNextEntry(ZipEntry e) throws IOException {
        ensureOpen();
        if (entry != null) {
            closeEntry();
        }
        if (e.time == -1) {
            e.setTime(System.currentTimeMillis());
        }
        if (e.method == -1) {
            e.method = method;
        }
        switch (e.method) {
        case DEFLATED: 
            if (e.size == -1 || e.csize == -1 || e.crc == -1) {
                e.flag = 8;
            } else if (e.size != -1 && e.csize != -1 && e.crc != -1) {
                e.flag = 0;
            } else {
                throw new ZipException("DEFLATED entry missing size, compressed size, or crc-32");
            }
            e.version = 20;
            break;
        
        case STORED: 
            if (e.size == -1) {
                e.size = e.csize;
            } else if (e.csize == -1) {
                e.csize = e.size;
            } else if (e.size != e.csize) {
                throw new ZipException("STORED entry where compressed != uncompressed size");
            }
            if (e.size == -1 || e.crc == -1) {
                throw new ZipException("STORED entry missing size, compressed size, or crc-32");
            }
            e.version = 10;
            e.flag = 0;
            break;
        
        default: 
            throw new ZipException("unsupported compression method");
        
        }
        e.offset = written;
        if (names.put(e.name, e) != null) {
            throw new ZipException("duplicate entry: " + e.name);
        }
        writeLOC(e);
        entries.addElement(e);
        entry = e;
    }
    
    public void closeEntry() throws IOException {
        ensureOpen();
        ZipEntry e = entry;
        if (e != null) {
            switch (e.method) {
            case DEFLATED: 
                def.finish();
                while (!def.finished()) {
                    deflate();
                }
                if ((e.flag & 8) == 0) {
                    if (e.size != def.getBytesRead()) {
                        throw new ZipException("invalid entry size (expected " + e.size + " but got " + def.getBytesRead() + " bytes)");
                    }
                    if (e.csize != def.getBytesWritten()) {
                        throw new ZipException("invalid entry compressed size (expected " + e.csize + " but got " + def.getBytesWritten() + " bytes)");
                    }
                    if (e.crc != crc.getValue()) {
                        throw new ZipException("invalid entry CRC-32 (expected 0x" + Long.toHexString(e.crc) + " but got 0x" + Long.toHexString(crc.getValue()) + ")");
                    }
                } else {
                    e.size = def.getBytesRead();
                    e.csize = def.getBytesWritten();
                    e.crc = crc.getValue();
                    writeEXT(e);
                }
                def.reset();
                written += e.csize;
                break;
            
            case STORED: 
                if (e.size != written - locoff) {
                    throw new ZipException("invalid entry size (expected " + e.size + " but got " + (written - locoff) + " bytes)");
                }
                if (e.crc != crc.getValue()) {
                    throw new ZipException("invalid entry crc-32 (expected 0x" + Long.toHexString(e.crc) + " but got 0x" + Long.toHexString(crc.getValue()) + ")");
                }
                break;
            
            default: 
                throw new InternalError("invalid compression method");
            
            }
            crc.reset();
            entry = null;
        }
    }
    
    public synchronized void write(byte[] b, int off, int len) throws IOException {
        ensureOpen();
        if (off < 0 || len < 0 || off > b.length - len) {
            throw new IndexOutOfBoundsException();
        } else if (len == 0) {
            return;
        }
        if (entry == null) {
            throw new ZipException("no current ZIP entry");
        }
        switch (entry.method) {
        case DEFLATED: 
            super.write(b, off, len);
            break;
        
        case STORED: 
            written += len;
            if (written - locoff > entry.size) {
                throw new ZipException("attempt to write past end of STORED entry");
            }
            out.write(b, off, len);
            break;
        
        default: 
            throw new InternalError("invalid compression method");
        
        }
        crc.update(b, off, len);
    }
    
    public void finish() throws IOException {
        ensureOpen();
        if (finished) {
            return;
        }
        if (entry != null) {
            closeEntry();
        }
        if (entries.size() < 1) {
            throw new ZipException("ZIP file must have at least one entry");
        }
        long off = written;
        Enumeration e = entries.elements();
        while (e.hasMoreElements()) {
            writeCEN((ZipEntry)(ZipEntry)e.nextElement());
        }
        writeEND(off, written - off);
        finished = true;
    }
    
    public void close() throws IOException {
        if (!closed) {
            super.close();
            closed = true;
        }
    }
    
    private void writeLOC(ZipEntry e) throws IOException {
        writeInt(LOCSIG);
        writeShort(e.version);
        writeShort(e.flag);
        writeShort(e.method);
        writeInt(e.time);
        if ((e.flag & 8) == 8) {
            writeInt(0);
            writeInt(0);
            writeInt(0);
        } else {
            writeInt(e.crc);
            writeInt(e.csize);
            writeInt(e.size);
        }
        byte[] nameBytes = getUTF8Bytes(e.name);
        writeShort(nameBytes.length);
        writeShort(e.extra != null ? e.extra.length : 0);
        writeBytes(nameBytes, 0, nameBytes.length);
        if (e.extra != null) {
            writeBytes(e.extra, 0, e.extra.length);
        }
        locoff = written;
    }
    
    private void writeEXT(ZipEntry e) throws IOException {
        writeInt(EXTSIG);
        writeInt(e.crc);
        writeInt(e.csize);
        writeInt(e.size);
    }
    
    private void writeCEN(ZipEntry e) throws IOException {
        writeInt(CENSIG);
        writeShort(e.version);
        writeShort(e.version);
        writeShort(e.flag);
        writeShort(e.method);
        writeInt(e.time);
        writeInt(e.crc);
        writeInt(e.csize);
        writeInt(e.size);
        byte[] nameBytes = getUTF8Bytes(e.name);
        writeShort(nameBytes.length);
        writeShort(e.extra != null ? e.extra.length : 0);
        byte[] commentBytes;
        if (e.comment != null) {
            commentBytes = getUTF8Bytes(e.comment);
            writeShort(commentBytes.length);
        } else {
            commentBytes = null;
            writeShort(0);
        }
        writeShort(0);
        writeShort(0);
        writeInt(0);
        writeInt(e.offset);
        writeBytes(nameBytes, 0, nameBytes.length);
        if (e.extra != null) {
            writeBytes(e.extra, 0, e.extra.length);
        }
        if (commentBytes != null) {
            writeBytes(commentBytes, 0, commentBytes.length);
        }
    }
    
    private void writeEND(long off, long len) throws IOException {
        writeInt(ENDSIG);
        writeShort(0);
        writeShort(0);
        writeShort(entries.size());
        writeShort(entries.size());
        writeInt(len);
        writeInt(off);
        if (comment != null) {
            byte[] b = getUTF8Bytes(comment);
            writeShort(b.length);
            writeBytes(b, 0, b.length);
        } else {
            writeShort(0);
        }
    }
    
    private void writeShort(int v) throws IOException {
        OutputStream out = this.out;
        out.write((v >>> 0) & 255);
        out.write((v >>> 8) & 255);
        written += 2;
    }
    
    private void writeInt(long v) throws IOException {
        OutputStream out = this.out;
        out.write((int)((v >>> 0) & 255));
        out.write((int)((v >>> 8) & 255));
        out.write((int)((v >>> 16) & 255));
        out.write((int)((v >>> 24) & 255));
        written += 4;
    }
    
    private void writeBytes(byte[] b, int off, int len) throws IOException {
        super.out.write(b, off, len);
        written += len;
    }
    
    static int getUTF8Length(String s) {
        int count = 0;
        for (int i = 0; i < s.length(); i++) {
            char ch = s.charAt(i);
            if (ch <= 127) {
                count++;
            } else if (ch <= 2047) {
                count += 2;
            } else {
                count += 3;
            }
        }
        return count;
    }
    
    private static byte[] getUTF8Bytes(String s) {
        char[] c = s.toCharArray();
        int len = c.length;
        int count = 0;
        for (int i = 0; i < len; i++) {
            int ch = c[i];
            if (ch <= 127) {
                count++;
            } else if (ch <= 2047) {
                count += 2;
            } else {
                count += 3;
            }
        }
        byte[] b = new byte[count];
        int off = 0;
        for (int i = 0; i < len; i++) {
            int ch = c[i];
            if (ch <= 127) {
                b[off++] = (byte)ch;
            } else if (ch <= 2047) {
                b[off++] = (byte)((ch >> 6) | 192);
                b[off++] = (byte)((ch & 63) | 128);
            } else {
                b[off++] = (byte)((ch >> 12) | 224);
                b[off++] = (byte)(((ch >> 6) & 63) | 128);
                b[off++] = (byte)((ch & 63) | 128);
            }
        }
        return b;
    }
}
