package java.util.concurrent;

import java.util.*;
import java.util.concurrent.locks.*;
import java.util.concurrent.atomic.*;

final class Semaphore$FairSync extends Semaphore$Sync {
    
    Semaphore$FairSync(int permits) {
        super(permits);
    }
    
    protected int tryAcquireShared(int acquires) {
        Thread current = Thread.currentThread();
        for (; ; ) {
            Thread first = getFirstQueuedThread();
            if (first != null && first != current) return -1;
            int available = getState();
            int remaining = available - acquires;
            if (remaining < 0 || compareAndSetState(available, remaining)) return remaining;
        }
    }
}
