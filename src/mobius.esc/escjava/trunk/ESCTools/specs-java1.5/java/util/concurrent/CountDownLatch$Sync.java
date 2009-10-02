package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.concurrent.atomic.*;

final class CountDownLatch$Sync extends AbstractQueuedSynchronizer {
    
    CountDownLatch$Sync(int count) {
        
        setState(count);
    }
    
    int getCount() {
        return getState();
    }
    
    public int tryAcquireShared(int acquires) {
        return getState() == 0 ? 1 : -1;
    }
    
    public boolean tryReleaseShared(int releases) {
        for (; ; ) {
            int c = getState();
            if (c == 0) return false;
            int nextc = c - 1;
            if (compareAndSetState(c, nextc)) return nextc == 0;
        }
    }
}
