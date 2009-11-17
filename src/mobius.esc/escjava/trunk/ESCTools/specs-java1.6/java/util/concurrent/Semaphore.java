package java.util.concurrent;

import java.util.*;
import java.util.concurrent.locks.*;
import java.util.concurrent.atomic.*;

public class Semaphore implements java.io.Serializable {
    private static final long serialVersionUID = -3222578661600680210L;
    private final Semaphore$Sync sync;
    {
    }
    {
    }
    {
    }
    
    public Semaphore(int permits) {
        
        sync = new Semaphore$NonfairSync(permits);
    }
    
    public Semaphore(int permits, boolean fair) {
        
        sync = (fair) ? new Semaphore$FairSync(permits) : new Semaphore$NonfairSync(permits);
    }
    
    public void acquire() throws InterruptedException {
        sync.acquireSharedInterruptibly(1);
    }
    
    public void acquireUninterruptibly() {
        sync.acquireShared(1);
    }
    
    public boolean tryAcquire() {
        return sync.nonfairTryAcquireShared(1) >= 0;
    }
    
    public boolean tryAcquire(long timeout, TimeUnit unit) throws InterruptedException {
        return sync.tryAcquireSharedNanos(1, unit.toNanos(timeout));
    }
    
    public void release() {
        sync.releaseShared(1);
    }
    
    public void acquire(int permits) throws InterruptedException {
        if (permits < 0) throw new IllegalArgumentException();
        sync.acquireSharedInterruptibly(permits);
    }
    
    public void acquireUninterruptibly(int permits) {
        if (permits < 0) throw new IllegalArgumentException();
        sync.acquireShared(permits);
    }
    
    public boolean tryAcquire(int permits) {
        if (permits < 0) throw new IllegalArgumentException();
        return sync.nonfairTryAcquireShared(permits) >= 0;
    }
    
    public boolean tryAcquire(int permits, long timeout, TimeUnit unit) throws InterruptedException {
        if (permits < 0) throw new IllegalArgumentException();
        return sync.tryAcquireSharedNanos(permits, unit.toNanos(timeout));
    }
    
    public void release(int permits) {
        if (permits < 0) throw new IllegalArgumentException();
        sync.releaseShared(permits);
    }
    
    public int availablePermits() {
        return sync.getPermits();
    }
    
    public int drainPermits() {
        return sync.drainPermits();
    }
    
    protected void reducePermits(int reduction) {
        if (reduction < 0) throw new IllegalArgumentException();
        sync.reducePermits(reduction);
    }
    
    public boolean isFair() {
        return sync instanceof Semaphore$FairSync;
    }
    
    public final boolean hasQueuedThreads() {
        return sync.hasQueuedThreads();
    }
    
    public final int getQueueLength() {
        return sync.getQueueLength();
    }
    
    protected Collection getQueuedThreads() {
        return sync.getQueuedThreads();
    }
    
    public String toString() {
        return super.toString() + "[Permits = " + sync.getPermits() + "]";
    }
}
