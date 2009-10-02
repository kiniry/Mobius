package java.util.concurrent.locks;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

final class ReentrantLock$FairSync extends ReentrantLock$Sync {
    
    ReentrantLock$FairSync() {
        
    }
    
    final void lock() {
        acquire(1);
    }
    
    protected final boolean tryAcquire(int acquires) {
        final Thread current = Thread.currentThread();
        int c = getState();
        if (c == 0) {
            Thread first = getFirstQueuedThread();
            if ((first == null || first == current) && compareAndSetState(0, acquires)) {
                owner = current;
                return true;
            }
        } else if (current == owner) {
            setState(c + acquires);
            return true;
        }
        return false;
    }
}
