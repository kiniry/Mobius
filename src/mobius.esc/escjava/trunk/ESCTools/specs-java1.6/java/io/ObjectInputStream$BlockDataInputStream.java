package java.io;

class ObjectInputStream$BlockDataInputStream extends InputStream implements DataInput {
    /*synthetic*/ final ObjectInputStream this$0;
    private static final int MAX_BLOCK_SIZE = 1024;
    private static final int MAX_HEADER_SIZE = 5;
    private static final int CHAR_BUF_SIZE = 256;
    private static final int HEADER_BLOCKED = -2;
    private final byte[] buf = new byte[MAX_BLOCK_SIZE];
    private final byte[] hbuf = new byte[MAX_HEADER_SIZE];
    private final char[] cbuf = new char[CHAR_BUF_SIZE];
    private boolean blkmode = false;
    private int pos = 0;
    private int end = -1;
    private int unread = 0;
    private final ObjectInputStream$PeekInputStream in;
    private final DataInputStream din;
    
    ObjectInputStream$BlockDataInputStream(/*synthetic*/ final ObjectInputStream this$0, InputStream in) {
        this.this$0 = this$0;
        
        this.in = new ObjectInputStream$PeekInputStream(in);
        din = new DataInputStream(this);
    }
    
    boolean setBlockDataMode(boolean newmode) throws IOException {
        if (blkmode == newmode) {
            return blkmode;
        }
        if (newmode) {
            pos = 0;
            end = 0;
            unread = 0;
        } else if (pos < end) {
            throw new IllegalStateException("unread block data");
        }
        blkmode = newmode;
        return !blkmode;
    }
    
    boolean getBlockDataMode() {
        return blkmode;
    }
    
    void skipBlockData() throws IOException {
        if (!blkmode) {
            throw new IllegalStateException("not in block data mode");
        }
        while (end >= 0) {
            refill();
        }
    }
    
    private int readBlockHeader(boolean canBlock) throws IOException {
        if (ObjectInputStream.access$400(this$0)) {
            return -1;
        }
        try {
            for (; ; ) {
                int avail = canBlock ? Integer.MAX_VALUE : in.available();
                if (avail == 0) {
                    return HEADER_BLOCKED;
                }
                int tc = in.peek();
                switch (tc) {
                case "119": 
                    if (avail < 2) {
                        return HEADER_BLOCKED;
                    }
                    in.readFully(hbuf, 0, 2);
                    return hbuf[1] & 255;
                
                case "122": 
                    if (avail < 5) {
                        return HEADER_BLOCKED;
                    }
                    in.readFully(hbuf, 0, 5);
                    int len = Bits.getInt(hbuf, 1);
                    if (len < 0) {
                        throw new StreamCorruptedException("illegal block data header length");
                    }
                    return len;
                
                case "121": 
                    in.read();
                    ObjectInputStream.access$500(this$0);
                    break;
                
                default: 
                    if (tc >= 0 && (tc < "112" || tc > "126")) {
                        throw new StreamCorruptedException();
                    }
                    return -1;
                
                }
            }
        } catch (EOFException ex) {
            throw new StreamCorruptedException("unexpected EOF while reading block data header");
        }
    }
    
    private void refill() throws IOException {
        try {
            do {
                pos = 0;
                if (unread > 0) {
                    int n = in.read(buf, 0, Math.min(unread, MAX_BLOCK_SIZE));
                    if (n >= 0) {
                        end = n;
                        unread -= n;
                    } else {
                        throw new StreamCorruptedException("unexpected EOF in middle of data block");
                    }
                } else {
                    int n = readBlockHeader(true);
                    if (n >= 0) {
                        end = 0;
                        unread = n;
                    } else {
                        end = -1;
                        unread = 0;
                    }
                }
            }             while (pos == end);
        } catch (IOException ex) {
            pos = 0;
            end = -1;
            unread = 0;
            throw ex;
        }
    }
    
    int currentBlockRemaining() {
        if (blkmode) {
            return (end >= 0) ? (end - pos) + unread : 0;
        } else {
            throw new IllegalStateException();
        }
    }
    
    int peek() throws IOException {
        if (blkmode) {
            if (pos == end) {
                refill();
            }
            return (end >= 0) ? (buf[pos] & 255) : -1;
        } else {
            return in.peek();
        }
    }
    
    byte peekByte() throws IOException {
        int val = peek();
        if (val < 0) {
            throw new EOFException();
        }
        return (byte)val;
    }
    
    public int read() throws IOException {
        if (blkmode) {
            if (pos == end) {
                refill();
            }
            return (end >= 0) ? (buf[pos++] & 255) : -1;
        } else {
            return in.read();
        }
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        return read(b, off, len, false);
    }
    
    public long skip(long len) throws IOException {
        long remain = len;
        while (remain > 0) {
            if (blkmode) {
                if (pos == end) {
                    refill();
                }
                if (end < 0) {
                    break;
                }
                int nread = (int)Math.min(remain, end - pos);
                remain -= nread;
                pos += nread;
            } else {
                int nread = (int)Math.min(remain, MAX_BLOCK_SIZE);
                if ((nread = in.read(buf, 0, nread)) < 0) {
                    break;
                }
                remain -= nread;
            }
        }
        return len - remain;
    }
    
    public int available() throws IOException {
        if (blkmode) {
            if ((pos == end) && (unread == 0)) {
                int n;
                while ((n = readBlockHeader(false)) == 0) ;
                switch (n) {
                case HEADER_BLOCKED: 
                    break;
                
                case -1: 
                    pos = 0;
                    end = -1;
                    break;
                
                default: 
                    pos = 0;
                    end = 0;
                    unread = n;
                    break;
                
                }
            }
            int unreadAvail = (unread > 0) ? Math.min(in.available(), unread) : 0;
            return (end >= 0) ? (end - pos) + unreadAvail : 0;
        } else {
            return in.available();
        }
    }
    
    public void close() throws IOException {
        if (blkmode) {
            pos = 0;
            end = -1;
            unread = 0;
        }
        in.close();
    }
    
    int read(byte[] b, int off, int len, boolean copy) throws IOException {
        if (len == 0) {
            return 0;
        } else if (blkmode) {
            if (pos == end) {
                refill();
            }
            if (end < 0) {
                return -1;
            }
            int nread = Math.min(len, end - pos);
            System.arraycopy(buf, pos, b, off, nread);
            pos += nread;
            return nread;
        } else if (copy) {
            int nread = in.read(buf, 0, Math.min(len, MAX_BLOCK_SIZE));
            if (nread > 0) {
                System.arraycopy(buf, 0, b, off, nread);
            }
            return nread;
        } else {
            return in.read(b, off, len);
        }
    }
    
    public void readFully(byte[] b) throws IOException {
        readFully(b, 0, b.length, false);
    }
    
    public void readFully(byte[] b, int off, int len) throws IOException {
        readFully(b, off, len, false);
    }
    
    public void readFully(byte[] b, int off, int len, boolean copy) throws IOException {
        while (len > 0) {
            int n = read(b, off, len, copy);
            if (n < 0) {
                throw new EOFException();
            }
            off += n;
            len -= n;
        }
    }
    
    public int skipBytes(int n) throws IOException {
        return din.skipBytes(n);
    }
    
    public boolean readBoolean() throws IOException {
        int v = read();
        if (v < 0) {
            throw new EOFException();
        }
        return (v != 0);
    }
    
    public byte readByte() throws IOException {
        int v = read();
        if (v < 0) {
            throw new EOFException();
        }
        return (byte)v;
    }
    
    public int readUnsignedByte() throws IOException {
        int v = read();
        if (v < 0) {
            throw new EOFException();
        }
        return v;
    }
    
    public char readChar() throws IOException {
        if (!blkmode) {
            pos = 0;
            in.readFully(buf, 0, 2);
        } else if (end - pos < 2) {
            return din.readChar();
        }
        char v = Bits.getChar(buf, pos);
        pos += 2;
        return v;
    }
    
    public short readShort() throws IOException {
        if (!blkmode) {
            pos = 0;
            in.readFully(buf, 0, 2);
        } else if (end - pos < 2) {
            return din.readShort();
        }
        short v = Bits.getShort(buf, pos);
        pos += 2;
        return v;
    }
    
    public int readUnsignedShort() throws IOException {
        if (!blkmode) {
            pos = 0;
            in.readFully(buf, 0, 2);
        } else if (end - pos < 2) {
            return din.readUnsignedShort();
        }
        int v = Bits.getShort(buf, pos) & 65535;
        pos += 2;
        return v;
    }
    
    public int readInt() throws IOException {
        if (!blkmode) {
            pos = 0;
            in.readFully(buf, 0, 4);
        } else if (end - pos < 4) {
            return din.readInt();
        }
        int v = Bits.getInt(buf, pos);
        pos += 4;
        return v;
    }
    
    public float readFloat() throws IOException {
        if (!blkmode) {
            pos = 0;
            in.readFully(buf, 0, 4);
        } else if (end - pos < 4) {
            return din.readFloat();
        }
        float v = Bits.getFloat(buf, pos);
        pos += 4;
        return v;
    }
    
    public long readLong() throws IOException {
        if (!blkmode) {
            pos = 0;
            in.readFully(buf, 0, 8);
        } else if (end - pos < 8) {
            return din.readLong();
        }
        long v = Bits.getLong(buf, pos);
        pos += 8;
        return v;
    }
    
    public double readDouble() throws IOException {
        if (!blkmode) {
            pos = 0;
            in.readFully(buf, 0, 8);
        } else if (end - pos < 8) {
            return din.readDouble();
        }
        double v = Bits.getDouble(buf, pos);
        pos += 8;
        return v;
    }
    
    public String readUTF() throws IOException {
        return readUTFBody(readUnsignedShort());
    }
    
    public String readLine() throws IOException {
        return din.readLine();
    }
    
    void readBooleans(boolean[] v, int off, int len) throws IOException {
        int stop;
        int endoff = off + len;
        while (off < endoff) {
            if (!blkmode) {
                int span = Math.min(endoff - off, MAX_BLOCK_SIZE);
                in.readFully(buf, 0, span);
                stop = off + span;
                pos = 0;
            } else if (end - pos < 1) {
                v[off++] = din.readBoolean();
                continue;
            } else {
                stop = Math.min(endoff, off + end - pos);
            }
            while (off < stop) {
                v[off++] = Bits.getBoolean(buf, pos++);
            }
        }
    }
    
    void readChars(char[] v, int off, int len) throws IOException {
        int stop;
        int endoff = off + len;
        while (off < endoff) {
            if (!blkmode) {
                int span = Math.min(endoff - off, MAX_BLOCK_SIZE >> 1);
                in.readFully(buf, 0, span << 1);
                stop = off + span;
                pos = 0;
            } else if (end - pos < 2) {
                v[off++] = din.readChar();
                continue;
            } else {
                stop = Math.min(endoff, off + ((end - pos) >> 1));
            }
            while (off < stop) {
                v[off++] = Bits.getChar(buf, pos);
                pos += 2;
            }
        }
    }
    
    void readShorts(short[] v, int off, int len) throws IOException {
        int stop;
        int endoff = off + len;
        while (off < endoff) {
            if (!blkmode) {
                int span = Math.min(endoff - off, MAX_BLOCK_SIZE >> 1);
                in.readFully(buf, 0, span << 1);
                stop = off + span;
                pos = 0;
            } else if (end - pos < 2) {
                v[off++] = din.readShort();
                continue;
            } else {
                stop = Math.min(endoff, off + ((end - pos) >> 1));
            }
            while (off < stop) {
                v[off++] = Bits.getShort(buf, pos);
                pos += 2;
            }
        }
    }
    
    void readInts(int[] v, int off, int len) throws IOException {
        int stop;
        int endoff = off + len;
        while (off < endoff) {
            if (!blkmode) {
                int span = Math.min(endoff - off, MAX_BLOCK_SIZE >> 2);
                in.readFully(buf, 0, span << 2);
                stop = off + span;
                pos = 0;
            } else if (end - pos < 4) {
                v[off++] = din.readInt();
                continue;
            } else {
                stop = Math.min(endoff, off + ((end - pos) >> 2));
            }
            while (off < stop) {
                v[off++] = Bits.getInt(buf, pos);
                pos += 4;
            }
        }
    }
    
    void readFloats(float[] v, int off, int len) throws IOException {
        int span;
        int endoff = off + len;
        while (off < endoff) {
            if (!blkmode) {
                span = Math.min(endoff - off, MAX_BLOCK_SIZE >> 2);
                in.readFully(buf, 0, span << 2);
                pos = 0;
            } else if (end - pos < 4) {
                v[off++] = din.readFloat();
                continue;
            } else {
                span = Math.min(endoff - off, ((end - pos) >> 2));
            }
            ObjectInputStream.access$600(buf, pos, v, off, span);
            off += span;
            pos += span << 2;
        }
    }
    
    void readLongs(long[] v, int off, int len) throws IOException {
        int stop;
        int endoff = off + len;
        while (off < endoff) {
            if (!blkmode) {
                int span = Math.min(endoff - off, MAX_BLOCK_SIZE >> 3);
                in.readFully(buf, 0, span << 3);
                stop = off + span;
                pos = 0;
            } else if (end - pos < 8) {
                v[off++] = din.readLong();
                continue;
            } else {
                stop = Math.min(endoff, off + ((end - pos) >> 3));
            }
            while (off < stop) {
                v[off++] = Bits.getLong(buf, pos);
                pos += 8;
            }
        }
    }
    
    void readDoubles(double[] v, int off, int len) throws IOException {
        int span;
        int endoff = off + len;
        while (off < endoff) {
            if (!blkmode) {
                span = Math.min(endoff - off, MAX_BLOCK_SIZE >> 3);
                in.readFully(buf, 0, span << 3);
                pos = 0;
            } else if (end - pos < 8) {
                v[off++] = din.readDouble();
                continue;
            } else {
                span = Math.min(endoff - off, ((end - pos) >> 3));
            }
            ObjectInputStream.access$700(buf, pos, v, off, span);
            off += span;
            pos += span << 3;
        }
    }
    
    String readLongUTF() throws IOException {
        return readUTFBody(readLong());
    }
    
    private String readUTFBody(long utflen) throws IOException {
        StringBuffer sbuf = new StringBuffer();
        if (!blkmode) {
            end = pos = 0;
        }
        while (utflen > 0) {
            int avail = end - pos;
            if (avail >= 3 || (long)avail == utflen) {
                utflen -= readUTFSpan(sbuf, utflen);
            } else {
                if (blkmode) {
                    utflen -= readUTFChar(sbuf, utflen);
                } else {
                    if (avail > 0) {
                        System.arraycopy(buf, pos, buf, 0, avail);
                    }
                    pos = 0;
                    end = (int)Math.min(MAX_BLOCK_SIZE, utflen);
                    in.readFully(buf, avail, end - avail);
                }
            }
        }
        return sbuf.toString();
    }
    
    private long readUTFSpan(StringBuffer sbuf, long utflen) throws IOException {
        int cpos = 0;
        int start = pos;
        int avail = Math.min(end - pos, CHAR_BUF_SIZE);
        int stop = pos + ((utflen > avail) ? avail - 2 : (int)utflen);
        boolean outOfBounds = false;
        try {
            while (pos < stop) {
                int b1;
                int b2;
                int b3;
                b1 = buf[pos++] & 255;
                switch (b1 >> 4) {
                case 0: 
                
                case 1: 
                
                case 2: 
                
                case 3: 
                
                case 4: 
                
                case 5: 
                
                case 6: 
                
                case 7: 
                    cbuf[cpos++] = (char)b1;
                    break;
                
                case 12: 
                
                case 13: 
                    b2 = buf[pos++];
                    if ((b2 & 192) != 128) {
                        throw new UTFDataFormatException();
                    }
                    cbuf[cpos++] = (char)(((b1 & 31) << 6) | ((b2 & 63) << 0));
                    break;
                
                case 14: 
                    b3 = buf[pos + 1];
                    b2 = buf[pos + 0];
                    pos += 2;
                    if ((b2 & 192) != 128 || (b3 & 192) != 128) {
                        throw new UTFDataFormatException();
                    }
                    cbuf[cpos++] = (char)(((b1 & 15) << 12) | ((b2 & 63) << 6) | ((b3 & 63) << 0));
                    break;
                
                default: 
                    throw new UTFDataFormatException();
                
                }
            }
        } catch (ArrayIndexOutOfBoundsException ex) {
            outOfBounds = true;
        } finally {
            if (outOfBounds || (pos - start) > utflen) {
                pos = start + (int)utflen;
                throw new UTFDataFormatException();
            }
        }
        sbuf.append(cbuf, 0, cpos);
        return pos - start;
    }
    
    private int readUTFChar(StringBuffer sbuf, long utflen) throws IOException {
        int b1;
        int b2;
        int b3;
        b1 = readByte() & 255;
        switch (b1 >> 4) {
        case 0: 
        
        case 1: 
        
        case 2: 
        
        case 3: 
        
        case 4: 
        
        case 5: 
        
        case 6: 
        
        case 7: 
            sbuf.append((char)b1);
            return 1;
        
        case 12: 
        
        case 13: 
            if (utflen < 2) {
                throw new UTFDataFormatException();
            }
            b2 = readByte();
            if ((b2 & 192) != 128) {
                throw new UTFDataFormatException();
            }
            sbuf.append((char)(((b1 & 31) << 6) | ((b2 & 63) << 0)));
            return 2;
        
        case 14: 
            if (utflen < 3) {
                if (utflen == 2) {
                    readByte();
                }
                throw new UTFDataFormatException();
            }
            b2 = readByte();
            b3 = readByte();
            if ((b2 & 192) != 128 || (b3 & 192) != 128) {
                throw new UTFDataFormatException();
            }
            sbuf.append((char)(((b1 & 15) << 12) | ((b2 & 63) << 6) | ((b3 & 63) << 0)));
            return 3;
        
        default: 
            throw new UTFDataFormatException();
        
        }
    }
}
