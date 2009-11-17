package java.util.concurrent.locks;

import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.*;

public class ReentrantReadWriteLock implements ReadWriteLock, java.io.Serializable {
    
    /*synthetic*/ static ReentrantReadWriteLock$Sync access$000(ReentrantReadWriteLock x0) {
        return x0.sync;
    }
    private static final long serialVersionUID = -6992448646407690164L;
    private final ReentrantReadWriteLock$ReadLock readerLock;
    private final ReentrantReadWriteLock$WriteLock writerLock;
    private final ReentrantReadWriteLock$Sync sync;
    
    public ReentrantReadWriteLock() {
        
        sync = new ReentrantReadWriteLock$NonfairSync();
        readerLock = new ReentrantReadWriteLock$ReadLock(this);
        writerLock = new ReentrantReadWriteLock$WriteLock(this);
    }
    
    public ReentrantReadWriteLock(boolean fair) {
        
        sync = (fair) ? new ReentrantReadWriteLock$FairSync() : new ReentrantReadWriteLock$NonfairSync();
        readerLock = new ReentrantReadWriteLock$ReadLock(this);
        writerLock = new ReentrantReadWriteLock$WriteLock(this);
    }
    
    public ReentrantReadWriteLock$WriteLock writeLock() {
        return writerLock;
    }
    
    public ReentrantReadWriteLock$ReadLock readLock() {
        return readerLock;
    }
    static final int SHARED_SHIFT = 16;
    static final int SHARED_UNIT = (1 << SHARED_SHIFT);
    static final int EXCLUSIVE_MASK = (1 << SHARED_SHIFT) - 1;
    
    static int sharedCount(int c) {
        return c >>> SHARED_SHIFT;
    }
    
    static int exclusiveCount(int c) {
        return c & EXCLUSIVE_MASK;
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    public final boolean isFair() {
        return sync instanceof ReentrantReadWriteLock$FairSync;
    }
    
    protected Thread getOwner() {
        return sync.getOwner();
    }
    
    public int getReadLockCount() {
        return sync.getReadLockCount();
    }
    
    public boolean isWriteLocked() {
        return sync.isWriteLocked();
    }
    
    public boolean isWriteLockedByCurrentThread() {
        return sync.isHeldExclusively();
    }
    
    public int getWriteHoldCount() {
        return sync.getWriteHoldCount();
    }
    
    protected Collection getQueuedWriterThreads() {
        return sync.getExclusiveQueuedThreads();
    }
    
    protected Collection getQueuedReaderThreads() {
        return sync.getSharedQueuedThreads();
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
        int c = sync.getCount();
        int w = exclusiveCount(c);
        int r = sharedCount(c);
        return super.toString() + "[Write locks = " + w + ", Read locks = " + r + "]";
    }
    
    /*synthetic public Lock writeLock() {
        return this.writeLock();
    } */
    
    /*synthetic public Lock readLock() {
        return this.readLock();
    } */
}
