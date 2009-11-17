package java.security;

import java.io.*;
import java.lang.reflect.*;

class Policy$2 implements PrivilegedAction {
    /*synthetic*/ final String val$pc;
    
    Policy$2(/*synthetic*/ final String val$pc) {
        this.val$pc = val$pc;
        
    }
    
    public Object run() {
        try {
            ClassLoader cl = ClassLoader.getSystemClassLoader();
            ClassLoader extcl = null;
            while (cl != null) {
                extcl = cl;
                cl = cl.getParent();
            }
            return (extcl != null ? Class.forName(val$pc, true, extcl).newInstance() : null);
        } catch (Exception e) {
            return null;
        }
    }
}
