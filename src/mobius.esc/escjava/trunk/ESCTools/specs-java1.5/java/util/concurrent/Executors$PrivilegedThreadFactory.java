package java.util.concurrent;

import java.util.*;
import java.security.AccessControlContext;
import java.security.AccessController;

class Executors$PrivilegedThreadFactory extends Executors$DefaultThreadFactory {
    
    /*synthetic*/ static AccessControlContext access$800(Executors$PrivilegedThreadFactory x0) {
        return x0.acc;
    }
    
    /*synthetic*/ static ClassLoader access$700(Executors$PrivilegedThreadFactory x0) {
        return x0.ccl;
    }
    private final ClassLoader ccl;
    private final AccessControlContext acc;
    
    Executors$PrivilegedThreadFactory() {
        
        this.ccl = Thread.currentThread().getContextClassLoader();
        this.acc = AccessController.getContext();
        acc.checkPermission(new RuntimePermission("setContextClassLoader"));
    }
    
    public Thread newThread(final Runnable r) {
        return super.newThread(new Executors$PrivilegedThreadFactory$1(this, r));
    }
}
