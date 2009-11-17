package java.util.concurrent.locks;

import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.*;

final class ReentrantReadWriteLock$FairSync extends ReentrantReadWriteLock$Sync {
    
    ReentrantReadWriteLock$FairSync() {
        
    }
    
    protected final boolean tryAcquire(int acquires) {
        acquires = ReentrantReadWriteLock.exclusiveCount(acquires);
        Thread current = Thread.currentThread();
        Thread first;
        int c = getState();
        int w = ReentrantReadWriteLock.exclusiveCount(c);
        if (w + acquires >= 65536) throw new Error("Maximum lock count exceeded");
        if ((w == 0 || current != owner) && (c != 0 || ((first = getFirstQueuedThread()) != null && first != current))) return false;
        if (!compareAndSetState(c, c + acquires)) return false;
        owner = current;
        return true;
    }
    
    protected final int tryAcquireShared(int acquires) {
        Thread current = Thread.currentThread();
        for (; ; ) {
            int c = getState();
            if (ReentrantReadWriteLock.exclusiveCount(c) != 0) {
                if (owner != current) return -1;
            } else {
                Thread first = getFirstQueuedThread();
                if (first != null && first != current) return -1;
            }
            int nextc = c + (acquires << 16);
            if (nextc < c) throw new Error("Maximum lock count exceeded");
            if (compareAndSetState(c, nextc)) return 1;
        }
    }
    
    final void wlock() {
        acquire(1);
    }
}
