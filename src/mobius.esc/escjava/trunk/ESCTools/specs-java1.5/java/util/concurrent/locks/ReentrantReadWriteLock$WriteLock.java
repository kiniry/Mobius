package java.util.concurrent.locks;

import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.*;

public class ReentrantReadWriteLock$WriteLock implements Lock, java.io.Serializable {
    private static final long serialVersionUID = -4992448646407690164L;
    private final ReentrantReadWriteLock$Sync sync;
    
    protected ReentrantReadWriteLock$WriteLock(ReentrantReadWriteLock lock) {
        
        sync = ReentrantReadWriteLock.access$000(lock);
    }
    
    public void lock() {
        sync.wlock();
    }
    
    public void lockInterruptibly() throws InterruptedException {
        sync.acquireInterruptibly(1);
    }
    
    public boolean tryLock() {
        return sync.nonfairTryAcquire(1);
    }
    
    public boolean tryLock(long timeout, TimeUnit unit) throws InterruptedException {
        return sync.tryAcquireNanos(1, unit.toNanos(timeout));
    }
    
    public void unlock() {
        sync.release(1);
    }
    
    public Condition newCondition() {
        return sync.newCondition();
    }
    
    public String toString() {
        Thread owner = sync.getOwner();
        return super.toString() + ((owner == null) ? "[Unlocked]" : "[Locked by thread " + owner.getName() + "]");
    }
}
