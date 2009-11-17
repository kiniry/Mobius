package java.util.concurrent.locks;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

final class ReentrantLock$NonfairSync extends ReentrantLock$Sync {
    
    ReentrantLock$NonfairSync() {
        
    }
    
    final void lock() {
        if (compareAndSetState(0, 1)) owner = Thread.currentThread(); else acquire(1);
    }
    
    protected final boolean tryAcquire(int acquires) {
        return nonfairTryAcquire(acquires);
    }
}
