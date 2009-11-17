package javax.xml.transform;

import java.security.*;
import java.net.*;
import java.io.*;
import java.util.*;

class SecuritySupport$1 implements PrivilegedAction {
    /*synthetic*/ final SecuritySupport this$0;
    
    SecuritySupport$1(/*synthetic*/ final SecuritySupport this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        ClassLoader cl = null;
        try {
            cl = Thread.currentThread().getContextClassLoader();
        } catch (SecurityException ex) {
        }
        return cl;
    }
}
