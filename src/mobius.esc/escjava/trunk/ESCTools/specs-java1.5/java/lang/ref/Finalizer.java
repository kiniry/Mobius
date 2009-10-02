package java.lang.ref;

import java.security.PrivilegedAction;
import java.security.AccessController;

final class Finalizer extends FinalReference {
    
    /*synthetic*/ static Finalizer access$400(Finalizer x0) {
        return x0.next;
    }
    
    /*synthetic*/ static Finalizer access$302(Finalizer x0) {
        return unfinalized = x0;
    }
    
    /*synthetic*/ static Finalizer access$300() {
        return unfinalized;
    }
    
    /*synthetic*/ static Object access$200() {
        return lock;
    }
    
    /*synthetic*/ static void access$100(Finalizer x0) {
        x0.runFinalizer();
    }
    
    /*synthetic*/ static ReferenceQueue access$000() {
        return queue;
    }
    
    static native void invokeFinalizeMethod(Object o) throws Throwable;
    private static ReferenceQueue queue = new ReferenceQueue();
    private static Finalizer unfinalized = null;
    private static Object lock = new Object();
    private Finalizer next = null;
    private Finalizer prev = null;
    
    private boolean hasBeenFinalized() {
        return (next == this);
    }
    
    private void add() {
        synchronized (lock) {
            if (unfinalized != null) {
                this.next = unfinalized;
                unfinalized.prev = this;
            }
            unfinalized = this;
        }
    }
    
    private void remove() {
        synchronized (lock) {
            if (unfinalized == this) {
                if (this.next != null) {
                    unfinalized = this.next;
                } else {
                    unfinalized = this.prev;
                }
            }
            if (this.next != null) {
                this.next.prev = this.prev;
            }
            if (this.prev != null) {
                this.prev.next = this.next;
            }
            this.next = this;
            this.prev = this;
        }
    }
    
    private Finalizer(Object finalizee) {
        super(finalizee, queue);
        add();
    }
    
    static void register(Object finalizee) {
        new Finalizer(finalizee);
    }
    
    private void runFinalizer() {
        synchronized (this) {
            if (hasBeenFinalized()) return;
            remove();
        }
        try {
            Object finalizee = this.get();
            if (finalizee != null && !(finalizee instanceof java.lang.Enum)) {
                invokeFinalizeMethod(finalizee);
                finalizee = null;
            }
        } catch (Throwable x) {
        }
        super.clear();
    }
    
    private static void forkSecondaryFinalizer(final Runnable proc) {
        PrivilegedAction pa = new Finalizer$1(proc);
        AccessController.doPrivileged(pa);
    }
    
    static void runFinalization() {
        forkSecondaryFinalizer(new Finalizer$2());
    }
    
    static void runAllFinalizers() {
        forkSecondaryFinalizer(new Finalizer$3());
    }
    {
    }
    static {
        ThreadGroup tg = Thread.currentThread().getThreadGroup();
        for (ThreadGroup tgn = tg; tgn != null; tg = tgn, tgn = tg.getParent()) ;
        Thread finalizer = new Finalizer$FinalizerThread(tg);
        finalizer.setPriority(Thread.MAX_PRIORITY - 2);
        finalizer.setDaemon(true);
        finalizer.start();
    }
}
