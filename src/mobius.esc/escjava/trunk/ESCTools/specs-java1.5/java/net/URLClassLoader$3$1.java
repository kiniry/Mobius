package java.net;

import java.security.PrivilegedAction;

class URLClassLoader$3$1 implements PrivilegedAction {
    /*synthetic*/ final URLClassLoader$3 this$1;
    
    URLClassLoader$3$1(/*synthetic*/ final URLClassLoader$3 this$1) {
        this.this$1 = this$1;
        
    }
    
    public Object run() {
        if (!this$1.val$e.hasMoreElements()) return null;
        return this$1.val$e.nextElement();
    }
}
