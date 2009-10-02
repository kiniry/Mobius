package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.concurrent.atomic.*;

public class CountDownLatch {
    {
    }
    private final CountDownLatch$Sync sync;
    
    public CountDownLatch(int count) {
        
        if (count < 0) throw new IllegalArgumentException("count < 0");
        this.sync = new CountDownLatch$Sync(count);
    }
    
    public void await() throws InterruptedException {
        sync.acquireSharedInterruptibly(1);
    }
    
    public boolean await(long timeout, TimeUnit unit) throws InterruptedException {
        return sync.tryAcquireSharedNanos(1, unit.toNanos(timeout));
    }
    
    public void countDown() {
        sync.releaseShared(1);
    }
    
    public long getCount() {
        return sync.getCount();
    }
    
    public String toString() {
        return super.toString() + "[Count = " + sync.getCount() + "]";
    }
}
