package java.lang;

import java.io.File;
import java.security.PrivilegedAction;

class ClassLoader$3 implements PrivilegedAction {
    /*synthetic*/ final File val$file;
    
    ClassLoader$3(/*synthetic*/ final File val$file) {
        this.val$file = val$file;
        
    }
    
    public Object run() {
        return new Boolean(val$file.exists());
    }
}
