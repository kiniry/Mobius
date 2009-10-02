package javax.xml.transform;

import java.security.*;
import java.net.*;
import java.io.*;
import java.util.*;

class SecuritySupport$2 implements PrivilegedAction {
    /*synthetic*/ final SecuritySupport this$0;
    /*synthetic*/ final String val$propName;
    
    SecuritySupport$2(/*synthetic*/ final SecuritySupport this$0, /*synthetic*/ final String val$propName) {
        this.this$0 = this$0;
        this.val$propName = val$propName;
        
    }
    
    public Object run() {
        return System.getProperty(val$propName);
    }
}
