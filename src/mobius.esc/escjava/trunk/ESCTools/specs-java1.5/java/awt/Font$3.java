package java.awt;

import java.io.*;
import java.security.PrivilegedExceptionAction;

class Font$3 implements PrivilegedExceptionAction {
    /*synthetic*/ final File val$tFile;
    
    Font$3(/*synthetic*/ final File val$tFile) {
        this.val$tFile = val$tFile;
        
    }
    
    public Void run() {
        val$tFile.delete();
        return null;
    }
    
    /*synthetic*/ public Object run() throws Exception {
        return this.run();
    }
}
