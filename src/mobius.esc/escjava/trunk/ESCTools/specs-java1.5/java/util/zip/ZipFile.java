package java.util.zip;

import java.io.InputStream;
import java.io.IOException;
import java.io.File;
import java.util.Vector;
import java.util.Enumeration;
import java.security.AccessController;
import java.nio.MappedByteBuffer;
import java.lang.reflect.*;

public class ZipFile implements ZipConstants {
    
    /*synthetic*/ static boolean access$1802(ZipFile x0, boolean x1) {
        return x0.mbUsed = x1;
    }
    
    /*synthetic*/ static MappedByteBuffer access$1700(ZipFile x0) {
        return x0.mappedBuffer;
    }
    
    /*synthetic*/ static long access$1600(long x0) {
        return getEntryOffset(x0);
    }
    
    /*synthetic*/ static int access$1500(long x0, long x1, long x2, byte[] x3, int x4, int x5) {
        return read(x0, x1, x2, x3, x4, x5);
    }
    
    /*synthetic*/ static void access$1400(ZipFile x0) throws IOException {
        x0.ensureOpenOrZipException();
    }
    
    /*synthetic*/ static long access$1300(long x0) {
        return getSize(x0);
    }
    
    /*synthetic*/ static long access$1200(long x0) {
        return getCSize(x0);
    }
    
    /*synthetic*/ static void access$1100(long x0, long x1) {
        freeEntry(x0, x1);
    }
    
    /*synthetic*/ static String access$1000(ZipFile x0) {
        return x0.name;
    }
    
    /*synthetic*/ static String access$900(long x0) {
        return getZipMessage(x0);
    }
    
    /*synthetic*/ static boolean access$800(ZipFile x0) {
        return x0.closeRequested;
    }
    
    /*synthetic*/ static long access$700(long x0, int x1) {
        return getNextEntry(x0, x1);
    }
    
    /*synthetic*/ static long access$600(ZipFile x0) {
        return x0.jzfile;
    }
    
    /*synthetic*/ static int access$500(ZipFile x0) {
        return x0.total;
    }
    
    /*synthetic*/ static void access$400(ZipFile x0) {
        x0.ensureOpen();
    }
    
    /*synthetic*/ static void access$300(ZipFile x0, Inflater x1) {
        x0.releaseInflater(x1);
    }
    
    /*synthetic*/ static Constructor access$102(Constructor x0) {
        return directByteBufferConstructor = x0;
    }
    
    /*synthetic*/ static Constructor access$100() {
        return directByteBufferConstructor;
    }
    
    /*synthetic*/ static void access$000(long x0) {
        close(x0);
    }
    private long jzfile;
    private String name;
    private int total;
    private MappedByteBuffer mappedBuffer;
    private ZipFile$ZipCloser closer;
    private boolean mbUsed;
    private boolean closeRequested;
    private static final int STORED = ZipEntry.STORED;
    private static final int DEFLATED = ZipEntry.DEFLATED;
    public static final int OPEN_READ = 1;
    public static final int OPEN_DELETE = 4;
    static {
        initIDs();
    }
    
    private static native void initIDs();
    
    public ZipFile(String name) throws IOException {
        this(new File(name), OPEN_READ);
    }
    {
    }
    private static Constructor directByteBufferConstructor = null;
    
    private static void initDBBConstructor() {
        AccessController.doPrivileged(new ZipFile$1());
    }
    
    private static MappedByteBuffer newMappedByteBuffer(int size, long addr, Runnable unmapper) {
        MappedByteBuffer dbb;
        if (directByteBufferConstructor == null) initDBBConstructor();
        try {
            dbb = (MappedByteBuffer)(MappedByteBuffer)directByteBufferConstructor.newInstance(new Object[]{new Integer(size), new Long(addr), unmapper});
        } catch (InstantiationException e) {
            throw new InternalError();
        } catch (IllegalAccessException e) {
            throw new InternalError();
        } catch (InvocationTargetException e) {
            throw new InternalError();
        }
        return dbb;
    }
    
    public ZipFile(File file, int mode) throws IOException {
        
        if (((mode & OPEN_READ) == 0) || ((mode & ~(OPEN_READ | OPEN_DELETE)) != 0)) {
            throw new IllegalArgumentException("Illegal mode: 0x" + Integer.toHexString(mode));
        }
        String name = file.getPath();
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkRead(name);
            if ((mode & OPEN_DELETE) != 0) {
                sm.checkDelete(name);
            }
        }
        long jzfileCopy = open(name, mode, file.lastModified());
        this.name = name;
        this.total = getTotal(jzfileCopy);
        this.mbUsed = false;
        long mappedAddr = getMappedAddr(jzfileCopy);
        long len = getMappedLen(jzfileCopy);
        if (mappedAddr != 0 && len < Integer.MAX_VALUE) {
            this.closer = new ZipFile$ZipCloser(jzfileCopy, null);
            this.mappedBuffer = newMappedByteBuffer((int)len, mappedAddr, this.closer);
        }
        jzfile = jzfileCopy;
    }
    
    private static native long open(String name, int mode, long lastModified);
    
    private static native int getTotal(long jzfile);
    
    private static native long getMappedAddr(long jzfile);
    
    private static native long getMappedLen(long jzfile);
    
    public ZipFile(File file) throws ZipException, IOException {
        this(file, OPEN_READ);
    }
    
    public ZipEntry getEntry(String name) {
        if (name == null) {
            throw new NullPointerException("name");
        }
        long jzentry = 0;
        synchronized (this) {
            ensureOpen();
            jzentry = getEntry(jzfile, name, true);
            if (jzentry != 0) {
                ZipEntry ze = new ZipEntry(name, jzentry);
                freeEntry(jzfile, jzentry);
                return ze;
            }
        }
        return null;
    }
    
    private static native long getEntry(long jzfile, String name, boolean addSlash);
    
    private static native void freeEntry(long jzfile, long jzentry);
    
    public InputStream getInputStream(ZipEntry entry) throws IOException {
        return getInputStream(entry.name);
    }
    
    private InputStream getInputStream(String name) throws IOException {
        if (name == null) {
            throw new NullPointerException("name");
        }
        long jzentry = 0;
        ZipFile$ZipFileInputStream in = null;
        synchronized (this) {
            ensureOpen();
            jzentry = getEntry(jzfile, name, false);
            if (jzentry == 0) {
                return null;
            }
            if (mappedBuffer != null) {
                in = new ZipFile$MappedZipFileInputStream(this, jzentry, name);
            } else {
                in = new ZipFile$ZipFileInputStream(this, jzentry);
            }
        }
        final ZipFile$ZipFileInputStream zfin = in;
        switch (getMethod(jzentry)) {
        case STORED: 
            return zfin;
        
        case DEFLATED: 
            long size = getSize(jzentry) + 2;
            if (size > 65536) size = 8192;
            if (size <= 0) size = 4096;
            return new ZipFile$2(this, zfin, getInflater(), (int)size, zfin);
        
        default: 
            throw new ZipException("invalid compression method");
        
        }
    }
    
    private static native int getMethod(long jzentry);
    
    private Inflater getInflater() {
        synchronized (inflaters) {
            int size = inflaters.size();
            if (size > 0) {
                Inflater inf = (Inflater)(Inflater)inflaters.remove(size - 1);
                inf.reset();
                return inf;
            } else {
                return new Inflater(true);
            }
        }
    }
    
    private void releaseInflater(Inflater inf) {
        synchronized (inflaters) {
            inflaters.add(inf);
        }
    }
    private Vector inflaters = new Vector();
    
    public String getName() {
        return name;
    }
    
    public Enumeration entries() {
        ensureOpen();
        return new ZipFile$3(this);
    }
    
    private static native long getNextEntry(long jzfile, int i);
    
    public int size() {
        ensureOpen();
        return total;
    }
    
    public void close() throws IOException {
        synchronized (this) {
            closeRequested = true;
            if (jzfile != 0) {
                long zf = this.jzfile;
                jzfile = 0;
                if (closer != null) {
                    if (!mbUsed) {
                        closer.setClosed();
                        close(zf);
                    }
                } else {
                    close(zf);
                }
                synchronized (inflaters) {
                    int size = inflaters.size();
                    for (int i = 0; i < size; i++) {
                        Inflater inf = (Inflater)(Inflater)inflaters.get(i);
                        inf.end();
                    }
                }
            }
        }
    }
    
    protected void finalize() throws IOException {
        close();
    }
    
    private static native void close(long jzfile);
    
    private void ensureOpen() {
        if (closeRequested) {
            throw new IllegalStateException("zip file closed");
        }
    }
    
    private void ensureOpenOrZipException() throws IOException {
        if (closeRequested) {
            throw new ZipException("ZipFile closed");
        }
    }
    {
    }
    {
    }
    
    private static native int read(long jzfile, long jzentry, long pos, byte[] b, int off, int len);
    
    private static native long getCSize(long jzentry);
    
    private static native long getSize(long jzentry);
    
    private static native long getEntryOffset(long jzentry);
    
    private static native String getZipMessage(long jzfile);
}
