package javax.xml.transform;

import java.security.*;
import java.net.*;
import java.io.*;
import java.util.*;

class SecuritySupport$3 implements PrivilegedExceptionAction {
    /*synthetic*/ final SecuritySupport this$0;
    /*synthetic*/ final File val$file;
    
    SecuritySupport$3(/*synthetic*/ final SecuritySupport this$0, /*synthetic*/ final File val$file) throws FileNotFoundException {
        this.this$0 = this$0;
        this.val$file = val$file;
        
    }
    
    public Object run() throws FileNotFoundException {
        return new FileInputStream(val$file);
    }
}
