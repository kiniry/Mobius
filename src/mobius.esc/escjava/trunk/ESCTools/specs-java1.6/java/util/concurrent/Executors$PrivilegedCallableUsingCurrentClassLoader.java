package java.util.concurrent;

import java.util.*;
import java.security.AccessControlContext;
import java.security.AccessController;

final class Executors$PrivilegedCallableUsingCurrentClassLoader implements Callable {
    
    /*synthetic*/ static Exception access$602(Executors$PrivilegedCallableUsingCurrentClassLoader x0, Exception x1) {
        return x0.exception = x1;
    }
    
    /*synthetic*/ static Callable access$500(Executors$PrivilegedCallableUsingCurrentClassLoader x0) {
        return x0.task;
    }
    
    /*synthetic*/ static Object access$402(Executors$PrivilegedCallableUsingCurrentClassLoader x0, Object x1) {
        return x0.result = x1;
    }
    
    /*synthetic*/ static ClassLoader access$300(Executors$PrivilegedCallableUsingCurrentClassLoader x0) {
        return x0.ccl;
    }
    private final ClassLoader ccl;
    private final AccessControlContext acc;
    private final Callable task;
    private Object result;
    private Exception exception;
    
    Executors$PrivilegedCallableUsingCurrentClassLoader(Callable task) {
        
        this.task = task;
        this.ccl = Thread.currentThread().getContextClassLoader();
        this.acc = AccessController.getContext();
        acc.checkPermission(new RuntimePermission("getContextClassLoader"));
        acc.checkPermission(new RuntimePermission("setContextClassLoader"));
    }
    
    public Object call() throws Exception {
        AccessController.doPrivileged(new Executors$PrivilegedCallableUsingCurrentClassLoader$1(this), acc);
        if (exception != null) throw exception; else return result;
    }
}
