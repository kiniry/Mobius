package java.io;

import java.nio.channels.FileChannel;
import sun.nio.ch.FileChannelImpl;

public class FileInputStream extends InputStream {
    private FileDescriptor fd;
    private FileChannel channel = null;
    
    public FileInputStream(String name) throws FileNotFoundException {
        this(name != null ? new File(name) : null);
    }
    
    public FileInputStream(File file) throws FileNotFoundException {
        
        String name = (file != null ? file.getPath() : null);
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkRead(name);
        }
        if (name == null) {
            throw new NullPointerException();
        }
        fd = new FileDescriptor();
        open(name);
    }
    
    public FileInputStream(FileDescriptor fdObj) {
        
        SecurityManager security = System.getSecurityManager();
        if (fdObj == null) {
            throw new NullPointerException();
        }
        if (security != null) {
            security.checkRead(fdObj);
        }
        fd = fdObj;
    }
    
    private native void open(String name) throws FileNotFoundException;
    
    public native int read() throws IOException;
    
    private native int readBytes(byte[] b, int off, int len) throws IOException;
    
    public int read(byte[] b) throws IOException {
        return readBytes(b, 0, b.length);
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        return readBytes(b, off, len);
    }
    
    public native long skip(long n) throws IOException;
    
    public native int available() throws IOException;
    
    public void close() throws IOException {
        if (channel != null) channel.close();
        close0();
    }
    
    public final FileDescriptor getFD() throws IOException {
        if (fd != null) return fd;
        throw new IOException();
    }
    
    public FileChannel getChannel() {
        synchronized (this) {
            if (channel == null) channel = FileChannelImpl.open(fd, true, false, this);
            return channel;
        }
    }
    
    private static native void initIDs();
    
    private native void close0() throws IOException;
    static {
        initIDs();
    }
    
    protected void finalize() throws IOException {
        if (fd != null) {
            if (fd != fd.in) {
                close();
            }
        }
    }
}
