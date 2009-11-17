package java.io;

import java.security.PrivilegedAction;

class ObjectStreamClass$EntryFuture$1 implements PrivilegedAction {
    /*synthetic*/ final ObjectStreamClass$EntryFuture this$0;
    
    ObjectStreamClass$EntryFuture$1(/*synthetic*/ final ObjectStreamClass$EntryFuture this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        Thread.currentThread().interrupt();
        return null;
    }
}
