package java.util.concurrent;

import java.util.*;
import java.security.PrivilegedAction;

class Executors$PrivilegedThreadFactory$1$1 implements PrivilegedAction {
    /*synthetic*/ final Executors$PrivilegedThreadFactory$1 this$1;
    
    Executors$PrivilegedThreadFactory$1$1(/*synthetic*/ final Executors$PrivilegedThreadFactory$1 this$1) {
        this.this$1 = this$1;
        
    }
    
    public Object run() {
        Thread.currentThread().setContextClassLoader(Executors.PrivilegedThreadFactory.access$700(this$1.this$0));
        this$1.val$r.run();
        return null;
    }
}
