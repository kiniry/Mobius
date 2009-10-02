package java.io;

import java.nio.channels.FileChannel;
import sun.nio.ch.FileChannelImpl;

public class RandomAccessFile implements DataOutput, DataInput, Closeable {
    private FileDescriptor fd;
    private FileChannel channel = null;
    private boolean rw;
    private static final int O_RDONLY = 1;
    private static final int O_RDWR = 2;
    private static final int O_SYNC = 4;
    private static final int O_DSYNC = 8;
    
    public RandomAccessFile(String name, String mode) throws FileNotFoundException {
        this(name != null ? new File(name) : null, mode);
    }
    
    public RandomAccessFile(File file, String mode) throws FileNotFoundException {
        
        String name = (file != null ? file.getPath() : null);
        int imode = -1;
        if (mode.equals("r")) imode = O_RDONLY; else if (mode.startsWith("rw")) {
            imode = O_RDWR;
            rw = true;
            if (mode.length() > 2) {
                if (mode.equals("rws")) imode |= O_SYNC; else if (mode.equals("rwd")) imode |= O_DSYNC; else imode = -1;
            }
        }
        if (imode < 0) throw new IllegalArgumentException("Illegal mode \"" + mode + "\" must be one of " + "\"r\", \"rw\", \"rws\"," + " or \"rwd\"");
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkRead(name);
            if (rw) {
                security.checkWrite(name);
            }
        }
        if (name == null) {
            throw new NullPointerException();
        }
        fd = new FileDescriptor();
        open(name, imode);
    }
    
    public final FileDescriptor getFD() throws IOException {
        if (fd != null) return fd;
        throw new IOException();
    }
    
    public final FileChannel getChannel() {
        synchronized (this) {
            if (channel == null) channel = FileChannelImpl.open(fd, true, rw, this);
            return channel;
        }
    }
    
    private native void open(String name, int mode) throws FileNotFoundException;
    
    public native int read() throws IOException;
    
    private native int readBytes(byte[] b, int off, int len) throws IOException;
    
    public int read(byte[] b, int off, int len) throws IOException {
        return readBytes(b, off, len);
    }
    
    public int read(byte[] b) throws IOException {
        return readBytes(b, 0, b.length);
    }
    
    public final void readFully(byte[] b) throws IOException {
        readFully(b, 0, b.length);
    }
    
    public final void readFully(byte[] b, int off, int len) throws IOException {
        int n = 0;
        do {
            int count = this.read(b, off + n, len - n);
            if (count < 0) throw new EOFException();
            n += count;
        }         while (n < len);
    }
    
    public int skipBytes(int n) throws IOException {
        long pos;
        long len;
        long newpos;
        if (n <= 0) {
            return 0;
        }
        pos = getFilePointer();
        len = length();
        newpos = pos + n;
        if (newpos > len) {
            newpos = len;
        }
        seek(newpos);
        return (int)(newpos - pos);
    }
    
    public native void write(int b) throws IOException;
    
    private native void writeBytes(byte[] b, int off, int len) throws IOException;
    
    public void write(byte[] b) throws IOException {
        writeBytes(b, 0, b.length);
    }
    
    public void write(byte[] b, int off, int len) throws IOException {
        writeBytes(b, off, len);
    }
    
    public native long getFilePointer() throws IOException;
    
    public native void seek(long pos) throws IOException;
    
    public native long length() throws IOException;
    
    public native void setLength(long newLength) throws IOException;
    
    public void close() throws IOException {
        if (channel != null) channel.close();
        close0();
    }
    
    public final boolean readBoolean() throws IOException {
        int ch = this.read();
        if (ch < 0) throw new EOFException();
        return (ch != 0);
    }
    
    public final byte readByte() throws IOException {
        int ch = this.read();
        if (ch < 0) throw new EOFException();
        return (byte)(ch);
    }
    
    public final int readUnsignedByte() throws IOException {
        int ch = this.read();
        if (ch < 0) throw new EOFException();
        return ch;
    }
    
    public final short readShort() throws IOException {
        int ch1 = this.read();
        int ch2 = this.read();
        if ((ch1 | ch2) < 0) throw new EOFException();
        return (short)((ch1 << 8) + (ch2 << 0));
    }
    
    public final int readUnsignedShort() throws IOException {
        int ch1 = this.read();
        int ch2 = this.read();
        if ((ch1 | ch2) < 0) throw new EOFException();
        return (ch1 << 8) + (ch2 << 0);
    }
    
    public final char readChar() throws IOException {
        int ch1 = this.read();
        int ch2 = this.read();
        if ((ch1 | ch2) < 0) throw new EOFException();
        return (char)((ch1 << 8) + (ch2 << 0));
    }
    
    public final int readInt() throws IOException {
        int ch1 = this.read();
        int ch2 = this.read();
        int ch3 = this.read();
        int ch4 = this.read();
        if ((ch1 | ch2 | ch3 | ch4) < 0) throw new EOFException();
        return ((ch1 << 24) + (ch2 << 16) + (ch3 << 8) + (ch4 << 0));
    }
    
    public final long readLong() throws IOException {
        return ((long)(readInt()) << 32) + (readInt() & 4294967295L);
    }
    
    public final float readFloat() throws IOException {
        return Float.intBitsToFloat(readInt());
    }
    
    public final double readDouble() throws IOException {
        return Double.longBitsToDouble(readLong());
    }
    
    public final String readLine() throws IOException {
        StringBuffer input = new StringBuffer();
        int c = -1;
        boolean eol = false;
        while (!eol) {
            switch (c = read()) {
            case -1: 
            
            case '\n': 
                eol = true;
                break;
            
            case '\r': 
                eol = true;
                long cur = getFilePointer();
                if ((read()) != '\n') {
                    seek(cur);
                }
                break;
            
            default: 
                input.append((char)c);
                break;
            
            }
        }
        if ((c == -1) && (input.length() == 0)) {
            return null;
        }
        return input.toString();
    }
    
    public final String readUTF() throws IOException {
        return DataInputStream.readUTF(this);
    }
    
    public final void writeBoolean(boolean v) throws IOException {
        write(v ? 1 : 0);
    }
    
    public final void writeByte(int v) throws IOException {
        write(v);
    }
    
    public final void writeShort(int v) throws IOException {
        write((v >>> 8) & 255);
        write((v >>> 0) & 255);
    }
    
    public final void writeChar(int v) throws IOException {
        write((v >>> 8) & 255);
        write((v >>> 0) & 255);
    }
    
    public final void writeInt(int v) throws IOException {
        write((v >>> 24) & 255);
        write((v >>> 16) & 255);
        write((v >>> 8) & 255);
        write((v >>> 0) & 255);
    }
    
    public final void writeLong(long v) throws IOException {
        write((int)(v >>> 56) & 255);
        write((int)(v >>> 48) & 255);
        write((int)(v >>> 40) & 255);
        write((int)(v >>> 32) & 255);
        write((int)(v >>> 24) & 255);
        write((int)(v >>> 16) & 255);
        write((int)(v >>> 8) & 255);
        write((int)(v >>> 0) & 255);
    }
    
    public final void writeFloat(float v) throws IOException {
        writeInt(Float.floatToIntBits(v));
    }
    
    public final void writeDouble(double v) throws IOException {
        writeLong(Double.doubleToLongBits(v));
    }
    
    public final void writeBytes(String s) throws IOException {
        int len = s.length();
        byte[] b = new byte[len];
        s.getBytes(0, len, b, 0);
        writeBytes(b, 0, len);
    }
    
    public final void writeChars(String s) throws IOException {
        int clen = s.length();
        int blen = 2 * clen;
        byte[] b = new byte[blen];
        char[] c = new char[clen];
        s.getChars(0, clen, c, 0);
        for (int i = 0, j = 0; i < clen; i++) {
            b[j++] = (byte)(c[i] >>> 8);
            b[j++] = (byte)(c[i] >>> 0);
        }
        writeBytes(b, 0, blen);
    }
    
    public final void writeUTF(String str) throws IOException {
        DataOutputStream.writeUTF(str, this);
    }
    
    private static native void initIDs();
    
    private native void close0() throws IOException;
    static {
        initIDs();
    }
}
