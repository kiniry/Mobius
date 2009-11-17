package java.net;

import java.security.PrivilegedAction;
import java.security.Permission;

class URLClassLoader$4 implements PrivilegedAction {
    /*synthetic*/ final URLClassLoader this$0;
    /*synthetic*/ final Permission val$fp;
    /*synthetic*/ final SecurityManager val$sm;
    
    URLClassLoader$4(/*synthetic*/ final URLClassLoader this$0, /*synthetic*/ final SecurityManager val$sm, /*synthetic*/ final Permission val$fp) {
        this.this$0 = this$0;
        this.val$sm = val$sm;
        this.val$fp = val$fp;
        
    }
    
    public Object run() throws SecurityException {
        val$sm.checkPermission(val$fp);
        return null;
    }
}
