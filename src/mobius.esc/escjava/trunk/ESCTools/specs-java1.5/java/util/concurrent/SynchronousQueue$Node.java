package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

final class SynchronousQueue$Node extends AbstractQueuedSynchronizer {
    private static final int ACK = 1;
    private static final int CANCEL = -1;
    Object item;
    SynchronousQueue$Node next;
    
    SynchronousQueue$Node(Object x) {
        
        item = x;
    }
    
    SynchronousQueue$Node(Object x, SynchronousQueue$Node n) {
        
        item = x;
        next = n;
    }
    
    protected boolean tryAcquire(int ignore) {
        return getState() != 0;
    }
    
    protected boolean tryRelease(int newState) {
        return compareAndSetState(0, newState);
    }
    
    private Object extract() {
        Object x = item;
        item = null;
        return x;
    }
    
    private void checkCancellationOnInterrupt(InterruptedException ie) throws InterruptedException {
        if (release(CANCEL)) throw ie;
        Thread.currentThread().interrupt();
    }
    
    boolean setItem(Object x) {
        item = x;
        return release(ACK);
    }
    
    Object getItem() {
        return (release(ACK)) ? extract() : null;
    }
    
    void waitForTake() throws InterruptedException {
        try {
            acquireInterruptibly(0);
        } catch (InterruptedException ie) {
            checkCancellationOnInterrupt(ie);
        }
    }
    
    Object waitForPut() throws InterruptedException {
        try {
            acquireInterruptibly(0);
        } catch (InterruptedException ie) {
            checkCancellationOnInterrupt(ie);
        }
        return extract();
    }
    
    boolean waitForTake(long nanos) throws InterruptedException {
        try {
            if (!tryAcquireNanos(0, nanos) && release(CANCEL)) return false;
        } catch (InterruptedException ie) {
            checkCancellationOnInterrupt(ie);
        }
        return true;
    }
    
    Object waitForPut(long nanos) throws InterruptedException {
        try {
            if (!tryAcquireNanos(0, nanos) && release(CANCEL)) return null;
        } catch (InterruptedException ie) {
            checkCancellationOnInterrupt(ie);
        }
        return extract();
    }
}
