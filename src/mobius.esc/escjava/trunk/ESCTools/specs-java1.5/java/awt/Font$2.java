package java.awt;

import java.io.*;
import java.security.PrivilegedExceptionAction;

class Font$2 implements PrivilegedExceptionAction {
    /*synthetic*/ final File val$tFile;
    
    Font$2(/*synthetic*/ final File val$tFile) throws FileNotFoundException {
        this.val$tFile = val$tFile;
        
    }
    
    public OutputStream run() throws IOException {
        return new FileOutputStream(val$tFile);
    }
    
    /*synthetic public Object run() throws Exception {
        return this.run();
    } */
}
