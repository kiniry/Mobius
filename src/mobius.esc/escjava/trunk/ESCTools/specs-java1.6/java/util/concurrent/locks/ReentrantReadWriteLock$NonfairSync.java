package java.util.concurrent.locks;

import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.*;

final class ReentrantReadWriteLock$NonfairSync extends ReentrantReadWriteLock$Sync {
    
    ReentrantReadWriteLock$NonfairSync() {
        
    }
    
    protected final boolean tryAcquire(int acquires) {
        return nonfairTryAcquire(acquires);
    }
    
    protected final int tryAcquireShared(int acquires) {
        return nonfairTryAcquireShared(acquires);
    }
    
    final void wlock() {
        if (compareAndSetState(0, 1)) owner = Thread.currentThread(); else acquire(1);
    }
}
