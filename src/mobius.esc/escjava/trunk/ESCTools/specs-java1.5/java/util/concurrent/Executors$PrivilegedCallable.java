package java.util.concurrent;

import java.util.*;
import java.security.AccessControlContext;
import java.security.AccessController;

final class Executors$PrivilegedCallable implements Callable {
    
    /*synthetic*/ static Exception access$202(Executors$PrivilegedCallable x0, Exception x1) {
        return x0.exception = x1;
    }
    
    /*synthetic*/ static Callable access$100(Executors$PrivilegedCallable x0) {
        return x0.task;
    }
    
    /*synthetic*/ static Object access$002(Executors$PrivilegedCallable x0, Object x1) {
        return x0.result = x1;
    }
    private final AccessControlContext acc;
    private final Callable task;
    private Object result;
    private Exception exception;
    
    Executors$PrivilegedCallable(Callable task) {
        
        this.task = task;
        this.acc = AccessController.getContext();
    }
    
    public Object call() throws Exception {
        AccessController.doPrivileged(new Executors$PrivilegedCallable$1(this), acc);
        if (exception != null) throw exception; else return result;
    }
}
