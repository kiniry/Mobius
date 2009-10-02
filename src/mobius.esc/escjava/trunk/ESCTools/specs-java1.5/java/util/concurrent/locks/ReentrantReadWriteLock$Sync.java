package java.util.concurrent.locks;

import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.*;

abstract class ReentrantReadWriteLock$Sync extends AbstractQueuedSynchronizer {
    
    ReentrantReadWriteLock$Sync() {
        
    }
    transient Thread owner;
    
    abstract void wlock();
    
    final boolean nonfairTryAcquire(int acquires) {
        acquires = ReentrantReadWriteLock.exclusiveCount(acquires);
        Thread current = Thread.currentThread();
        int c = getState();
        int w = ReentrantReadWriteLock.exclusiveCount(c);
        if (w + acquires >= 65536) throw new Error("Maximum lock count exceeded");
        if (c != 0 && (w == 0 || current != owner)) return false;
        if (!compareAndSetState(c, c + acquires)) return false;
        owner = current;
        return true;
    }
    
    final int nonfairTryAcquireShared(int acquires) {
        for (; ; ) {
            int c = getState();
            int nextc = c + (acquires << 16);
            if (nextc < c) throw new Error("Maximum lock count exceeded");
            if (ReentrantReadWriteLock.exclusiveCount(c) != 0 && owner != Thread.currentThread()) return -1;
            if (compareAndSetState(c, nextc)) return 1;
        }
    }
    
    protected final boolean tryRelease(int releases) {
        Thread current = Thread.currentThread();
        int c = getState();
        if (owner != current) throw new IllegalMonitorStateException();
        int nextc = c - releases;
        boolean free = false;
        if (ReentrantReadWriteLock.exclusiveCount(c) == releases) {
            free = true;
            owner = null;
        }
        setState(nextc);
        return free;
    }
    
    protected final boolean tryReleaseShared(int releases) {
        for (; ; ) {
            int c = getState();
            int nextc = c - (releases << 16);
            if (nextc < 0) throw new IllegalMonitorStateException();
            if (compareAndSetState(c, nextc)) return nextc == 0;
        }
    }
    
    protected final boolean isHeldExclusively() {
        return ReentrantReadWriteLock.exclusiveCount(getState()) != 0 && owner == Thread.currentThread();
    }
    
    final AbstractQueuedSynchronizer$ConditionObject newCondition() {
        return new AbstractQueuedSynchronizer$ConditionObject(this);
    }
    
    final Thread getOwner() {
        int c = ReentrantReadWriteLock.exclusiveCount(getState());
        Thread o = owner;
        return (c == 0) ? null : o;
    }
    
    final int getReadLockCount() {
        return ReentrantReadWriteLock.sharedCount(getState());
    }
    
    final boolean isWriteLocked() {
        return ReentrantReadWriteLock.exclusiveCount(getState()) != 0;
    }
    
    final int getWriteHoldCount() {
        int c = ReentrantReadWriteLock.exclusiveCount(getState());
        Thread o = owner;
        return (o == Thread.currentThread()) ? c : 0;
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        setState(0);
    }
    
    final int getCount() {
        return getState();
    }
}
