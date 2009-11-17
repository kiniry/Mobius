package java.util.concurrent;

import java.util.*;
import java.util.concurrent.locks.*;
import java.util.concurrent.atomic.*;

abstract class Semaphore$Sync extends AbstractQueuedSynchronizer {
    
    Semaphore$Sync(int permits) {
        
        setState(permits);
    }
    
    final int getPermits() {
        return getState();
    }
    
    final int nonfairTryAcquireShared(int acquires) {
        for (; ; ) {
            int available = getState();
            int remaining = available - acquires;
            if (remaining < 0 || compareAndSetState(available, remaining)) return remaining;
        }
    }
    
    protected final boolean tryReleaseShared(int releases) {
        for (; ; ) {
            int p = getState();
            if (compareAndSetState(p, p + releases)) return true;
        }
    }
    
    final void reducePermits(int reductions) {
        for (; ; ) {
            int current = getState();
            int next = current - reductions;
            if (compareAndSetState(current, next)) return;
        }
    }
    
    final int drainPermits() {
        for (; ; ) {
            int current = getState();
            if (current == 0 || compareAndSetState(current, 0)) return current;
        }
    }
}
