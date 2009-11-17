package java.lang.ref;

import java.security.PrivilegedAction;

class Finalizer$1 implements PrivilegedAction {
    /*synthetic*/ final Runnable val$proc;
    
    Finalizer$1(/*synthetic*/ final Runnable val$proc) {
        this.val$proc = val$proc;
        
    }
    
    public Object run() {
        ThreadGroup tg = Thread.currentThread().getThreadGroup();
        for (ThreadGroup tgn = tg; tgn != null; tg = tgn, tgn = tg.getParent()) ;
        Thread sft = new Thread(tg, val$proc, "Secondary finalizer");
        sft.start();
        try {
            sft.join();
        } catch (InterruptedException x) {
        }
        return null;
    }
}
