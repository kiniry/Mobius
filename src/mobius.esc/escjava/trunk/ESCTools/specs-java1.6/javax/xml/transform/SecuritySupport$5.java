package javax.xml.transform;

import java.security.*;
import java.net.*;
import java.io.*;
import java.util.*;

class SecuritySupport$5 implements PrivilegedAction {
    /*synthetic*/ final SecuritySupport this$0;
    /*synthetic*/ final File val$f;
    
    SecuritySupport$5(/*synthetic*/ final SecuritySupport this$0, /*synthetic*/ final File val$f) {
        this.this$0 = this$0;
        this.val$f = val$f;
        
    }
    
    public Object run() {
        return new Boolean(val$f.exists());
    }
}
