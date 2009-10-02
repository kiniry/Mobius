package java.security;

import java.io.*;
import java.lang.reflect.*;

class Policy$3 implements PrivilegedAction {
    /*synthetic*/ final Policy val$p;
    
    Policy$3(/*synthetic*/ final Policy val$p) {
        this.val$p = val$p;
        
    }
    
    public Object run() {
        return val$p.getClass().getProtectionDomain();
    }
}
