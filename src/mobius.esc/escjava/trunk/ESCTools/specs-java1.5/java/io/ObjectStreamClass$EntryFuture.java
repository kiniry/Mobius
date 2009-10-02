package java.io;

import java.security.AccessController;

class ObjectStreamClass$EntryFuture {
    
    /*synthetic*/ ObjectStreamClass$EntryFuture(java.io.ObjectStreamClass$1 x0) {
        this();
    }
    
    private ObjectStreamClass$EntryFuture() {
        
    }
    private static final Object unset = new Object();
    private final Thread owner = Thread.currentThread();
    private Object entry = unset;
    
    synchronized boolean set(Object entry) {
        if (this.entry != unset) {
            return false;
        }
        this.entry = entry;
        notifyAll();
        return true;
    }
    
    synchronized Object get() {
        boolean interrupted = false;
        while (entry == unset) {
            try {
                wait();
            } catch (InterruptedException ex) {
                interrupted = true;
            }
        }
        if (interrupted) {
            AccessController.doPrivileged(new ObjectStreamClass$EntryFuture$1(this));
        }
        return entry;
    }
    
    Thread getOwner() {
        return owner;
    }
}
