package javax.security.auth;

import java.util.*;
import java.io.*;
import java.lang.reflect.*;

class Subject$SecureSet$6 implements java.security.PrivilegedAction {
    /*synthetic*/ final Subject$SecureSet this$0;
    /*synthetic*/ final Iterator val$e;
    
    Subject$SecureSet$6(/*synthetic*/ final Subject$SecureSet this$0, /*synthetic*/ final Iterator val$e) {
        this.this$0 = this$0;
        this.val$e = val$e;
        
    }
    
    public Object run() {
        return val$e.next();
    }
}
