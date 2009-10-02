package java.util.concurrent.locks;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

public class ReentrantLock implements Lock, java.io.Serializable {
    private static final long serialVersionUID = 7373984872572414699L;
    private final ReentrantLock$Sync sync;
    {
    }
    {
    }
    {
    }
    
    public ReentrantLock() {
        
        sync = new ReentrantLock$NonfairSync();
    }
    
    public ReentrantLock(boolean fair) {
        
        sync = (fair) ? new ReentrantLock$FairSync() : new ReentrantLock$NonfairSync();
    }
    
    public void lock() {
        sync.lock();
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
    
    public int getHoldCount() {
        return sync.getHoldCount();
    }
    
    public boolean isHeldByCurrentThread() {
        return sync.isHeldExclusively();
    }
    
    public boolean isLocked() {
        return sync.isLocked();
    }
    
    public final boolean isFair() {
        return sync instanceof ReentrantLock$FairSync;
    }
    
    protected Thread getOwner() {
        return sync.getOwner();
    }
    
    public final boolean hasQueuedThreads() {
        return sync.hasQueuedThreads();
    }
    
    public final boolean hasQueuedThread(Thread thread) {
        return sync.isQueued(thread);
    }
    
    public final int getQueueLength() {
        return sync.getQueueLength();
    }
    
    protected Collection getQueuedThreads() {
        return sync.getQueuedThreads();
    }
    
    public boolean hasWaiters(Condition condition) {
        if (condition == null) throw new NullPointerException();
        if (!(condition instanceof AbstractQueuedSynchronizer$ConditionObject)) throw new IllegalArgumentException("not owner");
        return sync.hasWaiters((AbstractQueuedSynchronizer$ConditionObject)(AbstractQueuedSynchronizer$ConditionObject)condition);
    }
    
    public int getWaitQueueLength(Condition condition) {
        if (condition == null) throw new NullPointerException();
        if (!(condition instanceof AbstractQueuedSynchronizer$ConditionObject)) throw new IllegalArgumentException("not owner");
        return sync.getWaitQueueLength((AbstractQueuedSynchronizer$ConditionObject)(AbstractQueuedSynchronizer$ConditionObject)condition);
    }
    
    protected Collection getWaitingThreads(Condition condition) {
        if (condition == null) throw new NullPointerException();
        if (!(condition instanceof AbstractQueuedSynchronizer$ConditionObject)) throw new IllegalArgumentException("not owner");
        return sync.getWaitingThreads((AbstractQueuedSynchronizer$ConditionObject)(AbstractQueuedSynchronizer$ConditionObject)condition);
    }
    
    public String toString() {
        Thread owner = sync.getOwner();
        return super.toString() + ((owner == null) ? "[Unlocked]" : "[Locked by thread " + owner.getName() + "]");
    }
}
