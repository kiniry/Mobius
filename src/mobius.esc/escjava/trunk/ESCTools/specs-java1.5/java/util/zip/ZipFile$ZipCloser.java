package java.util.zip;

import java.lang.reflect.*;

class ZipFile$ZipCloser implements Runnable {
    
    /*synthetic*/ ZipFile$ZipCloser(long x0, java.util.zip.ZipFile$1 x1) {
        this(x0);
    }
    private long mappedFileID;
    
    private ZipFile$ZipCloser(long jzFile) {
        
        mappedFileID = jzFile;
    }
    
    public synchronized void setClosed() {
        mappedFileID = 0;
    }
    
    public synchronized void run() {
        if (mappedFileID != 0) {
            ZipFile.access$000(mappedFileID);
            mappedFileID = 0;
        }
    }
}
