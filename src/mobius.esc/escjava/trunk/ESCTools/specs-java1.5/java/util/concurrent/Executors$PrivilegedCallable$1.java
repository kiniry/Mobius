package java.util.concurrent;

import java.util.*;
import java.security.PrivilegedAction;

class Executors$PrivilegedCallable$1 implements PrivilegedAction {
    /*synthetic*/ final Executors$PrivilegedCallable this$0;
    
    Executors$PrivilegedCallable$1(/*synthetic*/ final Executors$PrivilegedCallable this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        try {
            Executors.PrivilegedCallable.access$002(this$0, Executors.PrivilegedCallable.access$100(this$0).call());
        } catch (Exception ex) {
            Executors.PrivilegedCallable.access$202(this$0, ex);
        }
        return null;
    }
}
