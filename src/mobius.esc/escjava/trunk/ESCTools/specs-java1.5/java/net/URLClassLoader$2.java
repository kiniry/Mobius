package java.net;

import java.security.PrivilegedAction;

class URLClassLoader$2 implements PrivilegedAction {
    /*synthetic*/ final URLClassLoader this$0;
    /*synthetic*/ final String val$name;
    
    URLClassLoader$2(/*synthetic*/ final URLClassLoader this$0, /*synthetic*/ final String val$name) {
        this.this$0 = this$0;
        this.val$name = val$name;
        
    }
    
    public Object run() {
        return URLClassLoader.access$000(this$0).findResource(val$name, true);
    }
}
