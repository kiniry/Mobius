package java.awt;

import java.io.*;
import java.security.PrivilegedExceptionAction;

class Font$1 implements PrivilegedExceptionAction {
    
    Font$1() throws IOException {
        
    }
    
    public File run() throws IOException {
        return File.createTempFile("+~JF", ".tmp", null);
    }
    
    /*synthetic public Object run() throws Exception {
        return this.run();
    } */
}
