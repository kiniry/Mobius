package java.util.concurrent.locks;

import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.*;

public class ReentrantReadWriteLock$ReadLock implements Lock, java.io.Serializable {
    private static final long serialVersionUID = -5992448646407690164L;
    private final ReentrantReadWriteLock$Sync sync;
    
    protected ReentrantReadWriteLock$ReadLock(ReentrantReadWriteLock lock) {
        
        sync = ReentrantReadWriteLock.access$000(lock);
    }
    
    public void lock() {
        sync.acquireShared(1);
    }
    
    public void lockInterruptibly() throws InterruptedException {
        sync.acquireSharedInterruptibly(1);
    }
    
    public boolean tryLock() {
        return sync.nonfairTryAcquireShared(1) >= 0;
    }
    
    public boolean tryLock(long timeout, TimeUnit unit) throws InterruptedException {
        return sync.tryAcquireSharedNanos(1, unit.toNanos(timeout));
    }
    
    public void unlock() {
        sync.releaseShared(1);
    }
    
    public Condition newCondition() {
        throw new UnsupportedOperationException();
    }
    
    public String toString() {
        int r = sync.getReadLockCount();
        return super.toString() + "[Read locks = " + r + "]";
    }
}
