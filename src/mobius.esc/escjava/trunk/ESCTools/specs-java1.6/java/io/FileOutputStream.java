package java.io;

import java.nio.channels.FileChannel;
import sun.nio.ch.FileChannelImpl;

public class FileOutputStream extends OutputStream {
    private FileDescriptor fd;
    private FileChannel channel = null;
    private boolean append = false;
    
    public FileOutputStream(String name) throws FileNotFoundException {
        this(name != null ? new File(name) : null, false);
    }
    
    public FileOutputStream(String name, boolean append) throws FileNotFoundException {
        this(name != null ? new File(name) : null, append);
    }
    
    public FileOutputStream(File file) throws FileNotFoundException {
        this(file, false);
    }
    
    public FileOutputStream(File file, boolean append) throws FileNotFoundException {
        
        String name = (file != null ? file.getPath() : null);
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkWrite(name);
        }
        if (name == null) {
            throw new NullPointerException();
        }
        fd = new FileDescriptor();
        this.append = append;
        if (append) {
            openAppend(name);
        } else {
            open(name);
        }
    }
    
    public FileOutputStream(FileDescriptor fdObj) {
        
        SecurityManager security = System.getSecurityManager();
        if (fdObj == null) {
            throw new NullPointerException();
        }
        if (security != null) {
            security.checkWrite(fdObj);
        }
        fd = fdObj;
    }
    
    private native void open(String name) throws FileNotFoundException;
    
    private native void openAppend(String name) throws FileNotFoundException;
    
    public native void write(int b) throws IOException;
    
    private native void writeBytes(byte[] b, int off, int len) throws IOException;
    
    public void write(byte[] b) throws IOException {
        writeBytes(b, 0, b.length);
    }
    
    public void write(byte[] b, int off, int len) throws IOException {
        writeBytes(b, off, len);
    }
    
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
            if (channel == null) channel = FileChannelImpl.open(fd, false, true, this, append);
            return channel;
        }
    }
    
    protected void finalize() throws IOException {
        if (fd != null) {
            if (fd == fd.out || fd == fd.err) {
                flush();
            } else {
                close();
            }
        }
    }
    
    private native void close0() throws IOException;
    
    private static native void initIDs();
    static {
        initIDs();
    }
}
