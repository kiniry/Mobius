package java.util.concurrent;

import java.util.*;
import java.security.PrivilegedAction;

class Executors$PrivilegedCallableUsingCurrentClassLoader$1 implements PrivilegedAction {
    /*synthetic*/ final Executors$PrivilegedCallableUsingCurrentClassLoader this$0;
    
    Executors$PrivilegedCallableUsingCurrentClassLoader$1(/*synthetic*/ final Executors$PrivilegedCallableUsingCurrentClassLoader this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        ClassLoader savedcl = null;
        Thread t = Thread.currentThread();
        try {
            ClassLoader cl = t.getContextClassLoader();
            if (Executors.PrivilegedCallableUsingCurrentClassLoader.access$300(this$0) != cl) {
                t.setContextClassLoader(Executors.PrivilegedCallableUsingCurrentClassLoader.access$300(this$0));
                savedcl = cl;
            }
            Executors.PrivilegedCallableUsingCurrentClassLoader.access$402(this$0, Executors.PrivilegedCallableUsingCurrentClassLoader.access$500(this$0).call());
        } catch (Exception ex) {
            Executors.PrivilegedCallableUsingCurrentClassLoader.access$602(this$0, ex);
        } finally {
            if (savedcl != null) t.setContextClassLoader(savedcl);
        }
        return null;
    }
}
