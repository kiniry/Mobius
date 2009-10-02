package java.util.concurrent;

import java.util.*;
import java.security.AccessController;

class Executors$PrivilegedThreadFactory$1 implements Runnable {
    /*synthetic*/ final Executors$PrivilegedThreadFactory this$0;
    /*synthetic*/ final Runnable val$r;
    
    Executors$PrivilegedThreadFactory$1(/*synthetic*/ final Executors$PrivilegedThreadFactory this$0, /*synthetic*/ final Runnable val$r) {
        this.this$0 = this$0;
        this.val$r = val$r;
        
    }
    
    public void run() {
        AccessController.doPrivileged(new Executors$PrivilegedThreadFactory$1$1(this), Executors.PrivilegedThreadFactory.access$800(this$0));
    }
}
