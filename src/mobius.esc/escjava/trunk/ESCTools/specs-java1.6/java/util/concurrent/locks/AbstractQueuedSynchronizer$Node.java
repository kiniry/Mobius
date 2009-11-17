package java.util.concurrent.locks;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

final class AbstractQueuedSynchronizer$Node {
    static final int CANCELLED = 1;
    static final int SIGNAL = -1;
    static final int CONDITION = -2;
    static final AbstractQueuedSynchronizer$Node SHARED = new AbstractQueuedSynchronizer$Node();
    static final AbstractQueuedSynchronizer$Node EXCLUSIVE = null;
    volatile int waitStatus;
    volatile AbstractQueuedSynchronizer$Node prev;
    volatile AbstractQueuedSynchronizer$Node next;
    volatile Thread thread;
    AbstractQueuedSynchronizer$Node nextWaiter;
    
    final boolean isShared() {
        return nextWaiter == SHARED;
    }
    
    final AbstractQueuedSynchronizer$Node predecessor() throws NullPointerException {
        AbstractQueuedSynchronizer$Node p = prev;
        if (p == null) throw new NullPointerException(); else return p;
    }
    
    AbstractQueuedSynchronizer$Node() {
        
    }
    
    AbstractQueuedSynchronizer$Node(Thread thread, AbstractQueuedSynchronizer$Node mode) {
        
        this.nextWaiter = mode;
        this.thread = thread;
    }
    
    AbstractQueuedSynchronizer$Node(Thread thread, int waitStatus) {
        
        this.waitStatus = waitStatus;
        this.thread = thread;
    }
}
