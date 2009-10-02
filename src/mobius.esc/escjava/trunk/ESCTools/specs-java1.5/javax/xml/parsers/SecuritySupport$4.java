package javax.xml.parsers;

import java.security.*;
import java.net.*;
import java.io.*;
import java.util.*;

class SecuritySupport$4 implements PrivilegedAction {
    /*synthetic*/ final SecuritySupport this$0;
    /*synthetic*/ final String val$name;
    /*synthetic*/ final ClassLoader val$cl;
    
    SecuritySupport$4(/*synthetic*/ final SecuritySupport this$0, /*synthetic*/ final ClassLoader val$cl, /*synthetic*/ final String val$name) {
        this.this$0 = this$0;
        this.val$cl = val$cl;
        this.val$name = val$name;
        
    }
    
    public Object run() {
        InputStream ris;
        if (val$cl == null) {
            ris = ClassLoader.getSystemResourceAsStream(val$name);
        } else {
            ris = val$cl.getResourceAsStream(val$name);
        }
        return ris;
    }
}
