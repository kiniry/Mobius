package java.lang;

import java.io.*;
import java.security.PrivilegedAction;
import sun.security.util.SecurityConstants;

class System$1 implements PrivilegedAction {
    /*synthetic*/ final SecurityManager val$s;
    
    System$1(/*synthetic*/ final SecurityManager val$s) {
        this.val$s = val$s;
        
    }
    
    public Object run() {
        val$s.getClass().getProtectionDomain().implies(SecurityConstants.ALL_PERMISSION);
        return null;
    }
}
