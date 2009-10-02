package java.util.concurrent.locks;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

abstract class ReentrantLock$Sync extends AbstractQueuedSynchronizer {
    
    ReentrantLock$Sync() {
        
    }
    transient Thread owner;
    
    abstract void lock();
    
    final boolean nonfairTryAcquire(int acquires) {
        final Thread current = Thread.currentThread();
        int c = getState();
        if (c == 0) {
            if (compareAndSetState(0, acquires)) {
                owner = current;
                return true;
            }
        } else if (current == owner) {
            setState(c + acquires);
            return true;
        }
        return false;
    }
    
    protected final boolean tryRelease(int releases) {
        int c = getState() - releases;
        if (Thread.currentThread() != owner) throw new IllegalMonitorStateException();
        boolean free = false;
        if (c == 0) {
            free = true;
            owner = null;
        }
        setState(c);
        return free;
    }
    
    protected final boolean isHeldExclusively() {
        return getState() != 0 && owner == Thread.currentThread();
    }
    
    final AbstractQueuedSynchronizer$ConditionObject newCondition() {
        return new AbstractQueuedSynchronizer$ConditionObject(this);
    }
    
    final Thread getOwner() {
        int c = getState();
        Thread o = owner;
        return (c == 0) ? null : o;
    }
    
    final int getHoldCount() {
        int c = getState();
        Thread o = owner;
        return (o == Thread.currentThread()) ? c : 0;
    }
    
    final boolean isLocked() {
        return getState() != 0;
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        setState(0);
    }
}
