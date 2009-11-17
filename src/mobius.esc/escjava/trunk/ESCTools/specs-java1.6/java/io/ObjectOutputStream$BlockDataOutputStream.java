package java.io;

class ObjectOutputStream$BlockDataOutputStream extends OutputStream implements DataOutput {
    private static final int MAX_BLOCK_SIZE = 1024;
    private static final int MAX_HEADER_SIZE = 5;
    private static final int CHAR_BUF_SIZE = 256;
    private final byte[] buf = new byte[MAX_BLOCK_SIZE];
    private final byte[] hbuf = new byte[MAX_HEADER_SIZE];
    private final char[] cbuf = new char[CHAR_BUF_SIZE];
    private boolean blkmode = false;
    private int pos = 0;
    private final OutputStream out;
    private final DataOutputStream dout;
    
    ObjectOutputStream$BlockDataOutputStream(OutputStream out) {
        
        this.out = out;
        dout = new DataOutputStream(this);
    }
    
    boolean setBlockDataMode(boolean mode) throws IOException {
        if (blkmode == mode) {
            return blkmode;
        }
        drain();
        blkmode = mode;
        return !blkmode;
    }
    
    boolean getBlockDataMode() {
        return blkmode;
    }
    
    public void write(int b) throws IOException {
        if (pos >= MAX_BLOCK_SIZE) {
            drain();
        }
        buf[pos++] = (byte)b;
    }
    
    public void write(byte[] b) throws IOException {
        write(b, 0, b.length, false);
    }
    
    public void write(byte[] b, int off, int len) throws IOException {
        write(b, off, len, false);
    }
    
    public void flush() throws IOException {
        drain();
        out.flush();
    }
    
    public void close() throws IOException {
        flush();
        out.close();
    }
    
    void write(byte[] b, int off, int len, boolean copy) throws IOException {
        if (!(copy || blkmode)) {
            drain();
            out.write(b, off, len);
            return;
        }
        while (len > 0) {
            if (pos >= MAX_BLOCK_SIZE) {
                drain();
            }
            if (len >= MAX_BLOCK_SIZE && !copy && pos == 0) {
                writeBlockHeader(MAX_BLOCK_SIZE);
                out.write(b, off, MAX_BLOCK_SIZE);
                off += MAX_BLOCK_SIZE;
                len -= MAX_BLOCK_SIZE;
            } else {
                int wlen = Math.min(len, MAX_BLOCK_SIZE - pos);
                System.arraycopy(b, off, buf, pos, wlen);
                pos += wlen;
                off += wlen;
                len -= wlen;
            }
        }
    }
    
    void drain() throws IOException {
        if (pos == 0) {
            return;
        }
        if (blkmode) {
            writeBlockHeader(pos);
        }
        out.write(buf, 0, pos);
        pos = 0;
    }
    
    private void writeBlockHeader(int len) throws IOException {
        if (len <= 255) {
            hbuf[0] = "119";
            hbuf[1] = (byte)len;
            out.write(hbuf, 0, 2);
        } else {
            hbuf[0] = "122";
            Bits.putInt(hbuf, 1, len);
            out.write(hbuf, 0, 5);
        }
    }
    
    public void writeBoolean(boolean v) throws IOException {
        if (pos >= MAX_BLOCK_SIZE) {
            drain();
        }
        Bits.putBoolean(buf, pos++, v);
    }
    
    public void writeByte(int v) throws IOException {
        if (pos >= MAX_BLOCK_SIZE) {
            drain();
        }
        buf[pos++] = (byte)v;
    }
    
    public void writeChar(int v) throws IOException {
        if (pos + 2 <= MAX_BLOCK_SIZE) {
            Bits.putChar(buf, pos, (char)v);
            pos += 2;
        } else {
            dout.writeChar(v);
        }
    }
    
    public void writeShort(int v) throws IOException {
        if (pos + 2 <= MAX_BLOCK_SIZE) {
            Bits.putShort(buf, pos, (short)v);
            pos += 2;
        } else {
            dout.writeShort(v);
        }
    }
    
    public void writeInt(int v) throws IOException {
        if (pos + 4 <= MAX_BLOCK_SIZE) {
            Bits.putInt(buf, pos, v);
            pos += 4;
        } else {
            dout.writeInt(v);
        }
    }
    
    public void writeFloat(float v) throws IOException {
        if (pos + 4 <= MAX_BLOCK_SIZE) {
            Bits.putFloat(buf, pos, v);
            pos += 4;
        } else {
            dout.writeFloat(v);
        }
    }
    
    public void writeLong(long v) throws IOException {
        if (pos + 8 <= MAX_BLOCK_SIZE) {
            Bits.putLong(buf, pos, v);
            pos += 8;
        } else {
            dout.writeLong(v);
        }
    }
    
    public void writeDouble(double v) throws IOException {
        if (pos + 8 <= MAX_BLOCK_SIZE) {
            Bits.putDouble(buf, pos, v);
            pos += 8;
        } else {
            dout.writeDouble(v);
        }
    }
    
    public void writeBytes(String s) throws IOException {
        int endoff = s.length();
        int cpos = 0;
        int csize = 0;
        for (int off = 0; off < endoff; ) {
            if (cpos >= csize) {
                cpos = 0;
                csize = Math.min(endoff - off, CHAR_BUF_SIZE);
                s.getChars(off, off + csize, cbuf, 0);
            }
            if (pos >= MAX_BLOCK_SIZE) {
                drain();
            }
            int n = Math.min(csize - cpos, MAX_BLOCK_SIZE - pos);
            int stop = pos + n;
            while (pos < stop) {
                buf[pos++] = (byte)cbuf[cpos++];
            }
            off += n;
        }
    }
    
    public void writeChars(String s) throws IOException {
        int endoff = s.length();
        for (int off = 0; off < endoff; ) {
            int csize = Math.min(endoff - off, CHAR_BUF_SIZE);
            s.getChars(off, off + csize, cbuf, 0);
            writeChars(cbuf, 0, csize);
            off += csize;
        }
    }
    
    public void writeUTF(String s) throws IOException {
        writeUTF(s, getUTFLength(s));
    }
    
    void writeBooleans(boolean[] v, int off, int len) throws IOException {
        int endoff = off + len;
        while (off < endoff) {
            if (pos >= MAX_BLOCK_SIZE) {
                drain();
            }
            int stop = Math.min(endoff, off + (MAX_BLOCK_SIZE - pos));
            while (off < stop) {
                Bits.putBoolean(buf, pos++, v[off++]);
            }
        }
    }
    
    void writeChars(char[] v, int off, int len) throws IOException {
        int limit = MAX_BLOCK_SIZE - 2;
        int endoff = off + len;
        while (off < endoff) {
            if (pos <= limit) {
                int avail = (MAX_BLOCK_SIZE - pos) >> 1;
                int stop = Math.min(endoff, off + avail);
                while (off < stop) {
                    Bits.putChar(buf, pos, v[off++]);
                    pos += 2;
                }
            } else {
                dout.writeChar(v[off++]);
            }
        }
    }
    
    void writeShorts(short[] v, int off, int len) throws IOException {
        int limit = MAX_BLOCK_SIZE - 2;
        int endoff = off + len;
        while (off < endoff) {
            if (pos <= limit) {
                int avail = (MAX_BLOCK_SIZE - pos) >> 1;
                int stop = Math.min(endoff, off + avail);
                while (off < stop) {
                    Bits.putShort(buf, pos, v[off++]);
                    pos += 2;
                }
            } else {
                dout.writeShort(v[off++]);
            }
        }
    }
    
    void writeInts(int[] v, int off, int len) throws IOException {
        int limit = MAX_BLOCK_SIZE - 4;
        int endoff = off + len;
        while (off < endoff) {
            if (pos <= limit) {
                int avail = (MAX_BLOCK_SIZE - pos) >> 2;
                int stop = Math.min(endoff, off + avail);
                while (off < stop) {
                    Bits.putInt(buf, pos, v[off++]);
                    pos += 4;
                }
            } else {
                dout.writeInt(v[off++]);
            }
        }
    }
    
    void writeFloats(float[] v, int off, int len) throws IOException {
        int limit = MAX_BLOCK_SIZE - 4;
        int endoff = off + len;
        while (off < endoff) {
            if (pos <= limit) {
                int avail = (MAX_BLOCK_SIZE - pos) >> 2;
                int chunklen = Math.min(endoff - off, avail);
                ObjectOutputStream.access$200(v, off, buf, pos, chunklen);
                off += chunklen;
                pos += chunklen << 2;
            } else {
                dout.writeFloat(v[off++]);
            }
        }
    }
    
    void writeLongs(long[] v, int off, int len) throws IOException {
        int limit = MAX_BLOCK_SIZE - 8;
        int endoff = off + len;
        while (off < endoff) {
            if (pos <= limit) {
                int avail = (MAX_BLOCK_SIZE - pos) >> 3;
                int stop = Math.min(endoff, off + avail);
                while (off < stop) {
                    Bits.putLong(buf, pos, v[off++]);
                    pos += 8;
                }
            } else {
                dout.writeLong(v[off++]);
            }
        }
    }
    
    void writeDoubles(double[] v, int off, int len) throws IOException {
        int limit = MAX_BLOCK_SIZE - 8;
        int endoff = off + len;
        while (off < endoff) {
            if (pos <= limit) {
                int avail = (MAX_BLOCK_SIZE - pos) >> 3;
                int chunklen = Math.min(endoff - off, avail);
                ObjectOutputStream.access$300(v, off, buf, pos, chunklen);
                off += chunklen;
                pos += chunklen << 3;
            } else {
                dout.writeDouble(v[off++]);
            }
        }
    }
    
    long getUTFLength(String s) {
        int len = s.length();
        long utflen = 0;
        for (int off = 0; off < len; ) {
            int csize = Math.min(len - off, CHAR_BUF_SIZE);
            s.getChars(off, off + csize, cbuf, 0);
            for (int cpos = 0; cpos < csize; cpos++) {
                char c = cbuf[cpos];
                if (c >= 1 && c <= 127) {
                    utflen++;
                } else if (c > 2047) {
                    utflen += 3;
                } else {
                    utflen += 2;
                }
            }
            off += csize;
        }
        return utflen;
    }
    
    void writeUTF(String s, long utflen) throws IOException {
        if (utflen > 65535L) {
            throw new UTFDataFormatException();
        }
        writeShort((int)utflen);
        if (utflen == (long)s.length()) {
            writeBytes(s);
        } else {
            writeUTFBody(s);
        }
    }
    
    void writeLongUTF(String s) throws IOException {
        writeLongUTF(s, getUTFLength(s));
    }
    
    void writeLongUTF(String s, long utflen) throws IOException {
        writeLong(utflen);
        if (utflen == (long)s.length()) {
            writeBytes(s);
        } else {
            writeUTFBody(s);
        }
    }
    
    private void writeUTFBody(String s) throws IOException {
        int limit = MAX_BLOCK_SIZE - 3;
        int len = s.length();
        for (int off = 0; off < len; ) {
            int csize = Math.min(len - off, CHAR_BUF_SIZE);
            s.getChars(off, off + csize, cbuf, 0);
            for (int cpos = 0; cpos < csize; cpos++) {
                char c = cbuf[cpos];
                if (pos <= limit) {
                    if (c <= 127 && c != 0) {
                        buf[pos++] = (byte)c;
                    } else if (c > 2047) {
                        buf[pos + 2] = (byte)(128 | ((c >> 0) & 63));
                        buf[pos + 1] = (byte)(128 | ((c >> 6) & 63));
                        buf[pos + 0] = (byte)(224 | ((c >> 12) & 15));
                        pos += 3;
                    } else {
                        buf[pos + 1] = (byte)(128 | ((c >> 0) & 63));
                        buf[pos + 0] = (byte)(192 | ((c >> 6) & 31));
                        pos += 2;
                    }
                } else {
                    if (c <= 127 && c != 0) {
                        write(c);
                    } else if (c > 2047) {
                        write(224 | ((c >> 12) & 15));
                        write(128 | ((c >> 6) & 63));
                        write(128 | ((c >> 0) & 63));
                    } else {
                        write(192 | ((c >> 6) & 31));
                        write(128 | ((c >> 0) & 63));
                    }
                }
            }
            off += csize;
        }
    }
}
