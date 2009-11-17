package java.util.concurrent.locks;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import sun.misc.Unsafe;

public abstract class AbstractQueuedSynchronizer implements java.io.Serializable {
    
    /*synthetic*/ static void access$000() {
        selfInterrupt();
    }
    private static final long serialVersionUID = 7373984972572414691L;
    
    protected AbstractQueuedSynchronizer() {
        
    }
    {
    }
    private volatile transient AbstractQueuedSynchronizer$Node head;
    private volatile transient AbstractQueuedSynchronizer$Node tail;
    private volatile int state;
    
    protected final int getState() {
        return state;
    }
    
    protected final void setState(int newState) {
        state = newState;
    }
    
    protected final boolean compareAndSetState(int expect, int update) {
        return unsafe.compareAndSwapInt(this, stateOffset, expect, update);
    }
    
    private AbstractQueuedSynchronizer$Node enq(final AbstractQueuedSynchronizer$Node node) {
        for (; ; ) {
            AbstractQueuedSynchronizer$Node t = tail;
            if (t == null) {
                AbstractQueuedSynchronizer$Node h = new AbstractQueuedSynchronizer$Node();
                h.next = node;
                node.prev = h;
                if (compareAndSetHead(h)) {
                    tail = node;
                    return h;
                }
            } else {
                node.prev = t;
                if (compareAndSetTail(t, node)) {
                    t.next = node;
                    return t;
                }
            }
        }
    }
    
    private AbstractQueuedSynchronizer$Node addWaiter(AbstractQueuedSynchronizer$Node mode) {
        AbstractQueuedSynchronizer$Node node = new AbstractQueuedSynchronizer$Node(Thread.currentThread(), mode);
        AbstractQueuedSynchronizer$Node pred = tail;
        if (pred != null) {
            node.prev = pred;
            if (compareAndSetTail(pred, node)) {
                pred.next = node;
                return node;
            }
        }
        enq(node);
        return node;
    }
    
    private void setHead(AbstractQueuedSynchronizer$Node node) {
        head = node;
        node.thread = null;
        node.prev = null;
    }
    
    private void unparkSuccessor(AbstractQueuedSynchronizer$Node node) {
        compareAndSetWaitStatus(node, AbstractQueuedSynchronizer$Node.SIGNAL, 0);
        Thread thread;
        AbstractQueuedSynchronizer$Node s = node.next;
        if (s != null && s.waitStatus <= 0) thread = s.thread; else {
            thread = null;
            for (s = tail; s != null && s != node; s = s.prev) if (s.waitStatus <= 0) thread = s.thread;
        }
        LockSupport.unpark(thread);
    }
    
    private void setHeadAndPropagate(AbstractQueuedSynchronizer$Node node, int propagate) {
        setHead(node);
        if (propagate > 0 && node.waitStatus != 0) {
            AbstractQueuedSynchronizer$Node s = node.next;
            if (s == null || s.isShared()) unparkSuccessor(node);
        }
    }
    
    private void cancelAcquire(AbstractQueuedSynchronizer$Node node) {
        if (node == null) return;
        node.thread = null;
        AbstractQueuedSynchronizer$Node pred = node.prev;
        while (pred.waitStatus > 0) node.prev = pred = pred.prev;
        AbstractQueuedSynchronizer$Node predNext = pred.next;
        node.waitStatus = AbstractQueuedSynchronizer$Node.CANCELLED;
        if (node == tail && compareAndSetTail(node, pred)) {
            compareAndSetNext(pred, predNext, null);
        } else {
            if (pred != head && (pred.waitStatus == AbstractQueuedSynchronizer$Node.SIGNAL || compareAndSetWaitStatus(pred, 0, AbstractQueuedSynchronizer$Node.SIGNAL)) && pred.thread != null) {
                AbstractQueuedSynchronizer$Node next = node.next;
                if (next != null && next.waitStatus <= 0) compareAndSetNext(pred, predNext, next);
            } else {
                unparkSuccessor(node);
            }
            node.next = node;
        }
    }
    
    private static boolean shouldParkAfterFailedAcquire(AbstractQueuedSynchronizer$Node pred, AbstractQueuedSynchronizer$Node node) {
        int s = pred.waitStatus;
        if (s < 0) return true;
        if (s > 0) {
            do {
                node.prev = pred = pred.prev;
            }             while (pred.waitStatus > 0);
            pred.next = node;
        } else compareAndSetWaitStatus(pred, 0, AbstractQueuedSynchronizer$Node.SIGNAL);
        return false;
    }
    
    private static void selfInterrupt() {
        Thread.currentThread().interrupt();
    }
    
    private static boolean parkAndCheckInterrupt() {
        LockSupport.park();
        return Thread.interrupted();
    }
    
    final boolean acquireQueued(final AbstractQueuedSynchronizer$Node node, int arg) {
        try {
            boolean interrupted = false;
            for (; ; ) {
                final AbstractQueuedSynchronizer$Node p = node.predecessor();
                if (p == head && tryAcquire(arg)) {
                    setHead(node);
                    p.next = null;
                    return interrupted;
                }
                if (shouldParkAfterFailedAcquire(p, node) && parkAndCheckInterrupt()) interrupted = true;
            }
        } catch (RuntimeException ex) {
            cancelAcquire(node);
            throw ex;
        }
    }
    
    private void doAcquireInterruptibly(int arg) throws InterruptedException {
        final AbstractQueuedSynchronizer$Node node = addWaiter(AbstractQueuedSynchronizer$Node.EXCLUSIVE);
        try {
            for (; ; ) {
                final AbstractQueuedSynchronizer$Node p = node.predecessor();
                if (p == head && tryAcquire(arg)) {
                    setHead(node);
                    p.next = null;
                    return;
                }
                if (shouldParkAfterFailedAcquire(p, node) && parkAndCheckInterrupt()) break;
            }
        } catch (RuntimeException ex) {
            cancelAcquire(node);
            throw ex;
        }
        cancelAcquire(node);
        throw new InterruptedException();
    }
    
    private boolean doAcquireNanos(int arg, long nanosTimeout) throws InterruptedException {
        long lastTime = System.nanoTime();
        final AbstractQueuedSynchronizer$Node node = addWaiter(AbstractQueuedSynchronizer$Node.EXCLUSIVE);
        try {
            for (; ; ) {
                final AbstractQueuedSynchronizer$Node p = node.predecessor();
                if (p == head && tryAcquire(arg)) {
                    setHead(node);
                    p.next = null;
                    return true;
                }
                if (nanosTimeout <= 0) {
                    cancelAcquire(node);
                    return false;
                }
                if (shouldParkAfterFailedAcquire(p, node)) {
                    LockSupport.parkNanos(nanosTimeout);
                    if (Thread.interrupted()) break;
                    long now = System.nanoTime();
                    nanosTimeout -= now - lastTime;
                    lastTime = now;
                }
            }
        } catch (RuntimeException ex) {
            cancelAcquire(node);
            throw ex;
        }
        cancelAcquire(node);
        throw new InterruptedException();
    }
    
    private void doAcquireShared(int arg) {
        final AbstractQueuedSynchronizer$Node node = addWaiter(AbstractQueuedSynchronizer$Node.SHARED);
        try {
            boolean interrupted = false;
            for (; ; ) {
                final AbstractQueuedSynchronizer$Node p = node.predecessor();
                if (p == head) {
                    int r = tryAcquireShared(arg);
                    if (r >= 0) {
                        setHeadAndPropagate(node, r);
                        p.next = null;
                        if (interrupted) selfInterrupt();
                        return;
                    }
                }
                if (shouldParkAfterFailedAcquire(p, node) && parkAndCheckInterrupt()) interrupted = true;
            }
        } catch (RuntimeException ex) {
            cancelAcquire(node);
            throw ex;
        }
    }
    
    private void doAcquireSharedInterruptibly(int arg) throws InterruptedException {
        final AbstractQueuedSynchronizer$Node node = addWaiter(AbstractQueuedSynchronizer$Node.SHARED);
        try {
            for (; ; ) {
                final AbstractQueuedSynchronizer$Node p = node.predecessor();
                if (p == head) {
                    int r = tryAcquireShared(arg);
                    if (r >= 0) {
                        setHeadAndPropagate(node, r);
                        p.next = null;
                        return;
                    }
                }
                if (shouldParkAfterFailedAcquire(p, node) && parkAndCheckInterrupt()) break;
            }
        } catch (RuntimeException ex) {
            cancelAcquire(node);
            throw ex;
        }
        cancelAcquire(node);
        throw new InterruptedException();
    }
    
    private boolean doAcquireSharedNanos(int arg, long nanosTimeout) throws InterruptedException {
        long lastTime = System.nanoTime();
        final AbstractQueuedSynchronizer$Node node = addWaiter(AbstractQueuedSynchronizer$Node.SHARED);
        try {
            for (; ; ) {
                final AbstractQueuedSynchronizer$Node p = node.predecessor();
                if (p == head) {
                    int r = tryAcquireShared(arg);
                    if (r >= 0) {
                        setHeadAndPropagate(node, r);
                        p.next = null;
                        return true;
                    }
                }
                if (nanosTimeout <= 0) {
                    cancelAcquire(node);
                    return false;
                }
                if (shouldParkAfterFailedAcquire(p, node)) {
                    LockSupport.parkNanos(nanosTimeout);
                    if (Thread.interrupted()) break;
                    long now = System.nanoTime();
                    nanosTimeout -= now - lastTime;
                    lastTime = now;
                }
            }
        } catch (RuntimeException ex) {
            cancelAcquire(node);
            throw ex;
        }
        cancelAcquire(node);
        throw new InterruptedException();
    }
    
    protected boolean tryAcquire(int arg) {
        throw new UnsupportedOperationException();
    }
    
    protected boolean tryRelease(int arg) {
        throw new UnsupportedOperationException();
    }
    
    protected int tryAcquireShared(int arg) {
        throw new UnsupportedOperationException();
    }
    
    protected boolean tryReleaseShared(int arg) {
        throw new UnsupportedOperationException();
    }
    
    protected boolean isHeldExclusively() {
        throw new UnsupportedOperationException();
    }
    
    public final void acquire(int arg) {
        if (!tryAcquire(arg) && acquireQueued(addWaiter(AbstractQueuedSynchronizer$Node.EXCLUSIVE), arg)) selfInterrupt();
    }
    
    public final void acquireInterruptibly(int arg) throws InterruptedException {
        if (Thread.interrupted()) throw new InterruptedException();
        if (!tryAcquire(arg)) doAcquireInterruptibly(arg);
    }
    
    public final boolean tryAcquireNanos(int arg, long nanosTimeout) throws InterruptedException {
        if (Thread.interrupted()) throw new InterruptedException();
        return tryAcquire(arg) || doAcquireNanos(arg, nanosTimeout);
    }
    
    public final boolean release(int arg) {
        if (tryRelease(arg)) {
            AbstractQueuedSynchronizer$Node h = head;
            if (h != null && h.waitStatus != 0) unparkSuccessor(h);
            return true;
        }
        return false;
    }
    
    public final void acquireShared(int arg) {
        if (tryAcquireShared(arg) < 0) doAcquireShared(arg);
    }
    
    public final void acquireSharedInterruptibly(int arg) throws InterruptedException {
        if (Thread.interrupted()) throw new InterruptedException();
        if (tryAcquireShared(arg) < 0) doAcquireSharedInterruptibly(arg);
    }
    
    public final boolean tryAcquireSharedNanos(int arg, long nanosTimeout) throws InterruptedException {
        if (Thread.interrupted()) throw new InterruptedException();
        return tryAcquireShared(arg) >= 0 || doAcquireSharedNanos(arg, nanosTimeout);
    }
    
    public final boolean releaseShared(int arg) {
        if (tryReleaseShared(arg)) {
            AbstractQueuedSynchronizer$Node h = head;
            if (h != null && h.waitStatus != 0) unparkSuccessor(h);
            return true;
        }
        return false;
    }
    
    public final boolean hasQueuedThreads() {
        return head != tail;
    }
    
    public final boolean hasContended() {
        return head != null;
    }
    
    public final Thread getFirstQueuedThread() {
        return (head == tail) ? null : fullGetFirstQueuedThread();
    }
    
    private Thread fullGetFirstQueuedThread() {
        AbstractQueuedSynchronizer$Node h = head;
        if (h == null) return null;
        AbstractQueuedSynchronizer$Node s = h.next;
        if (s != null) {
            Thread st = s.thread;
            AbstractQueuedSynchronizer$Node sp = s.prev;
            if (st != null && sp == head) return st;
        }
        AbstractQueuedSynchronizer$Node t = tail;
        Thread firstThread = null;
        while (t != null && t != head) {
            Thread tt = t.thread;
            if (tt != null) firstThread = tt;
            t = t.prev;
        }
        return firstThread;
    }
    
    public final boolean isQueued(Thread thread) {
        if (thread == null) throw new NullPointerException();
        for (AbstractQueuedSynchronizer$Node p = tail; p != null; p = p.prev) if (p.thread == thread) return true;
        return false;
    }
    
    public final int getQueueLength() {
        int n = 0;
        for (AbstractQueuedSynchronizer$Node p = tail; p != null; p = p.prev) {
            if (p.thread != null) ++n;
        }
        return n;
    }
    
    public final Collection getQueuedThreads() {
        ArrayList list = new ArrayList();
        for (AbstractQueuedSynchronizer$Node p = tail; p != null; p = p.prev) {
            Thread t = p.thread;
            if (t != null) list.add(t);
        }
        return list;
    }
    
    public final Collection getExclusiveQueuedThreads() {
        ArrayList list = new ArrayList();
        for (AbstractQueuedSynchronizer$Node p = tail; p != null; p = p.prev) {
            if (!p.isShared()) {
                Thread t = p.thread;
                if (t != null) list.add(t);
            }
        }
        return list;
    }
    
    public final Collection getSharedQueuedThreads() {
        ArrayList list = new ArrayList();
        for (AbstractQueuedSynchronizer$Node p = tail; p != null; p = p.prev) {
            if (p.isShared()) {
                Thread t = p.thread;
                if (t != null) list.add(t);
            }
        }
        return list;
    }
    
    public String toString() {
        int s = getState();
        String q = hasQueuedThreads() ? "non" : "";
        return super.toString() + "[State = " + s + ", " + q + "empty queue]";
    }
    
    final boolean isOnSyncQueue(AbstractQueuedSynchronizer$Node node) {
        if (node.waitStatus == AbstractQueuedSynchronizer$Node.CONDITION || node.prev == null) return false;
        if (node.next != null) return true;
        return findNodeFromTail(node);
    }
    
    private boolean findNodeFromTail(AbstractQueuedSynchronizer$Node node) {
        AbstractQueuedSynchronizer$Node t = tail;
        for (; ; ) {
            if (t == node) return true;
            if (t == null) return false;
            t = t.prev;
        }
    }
    
    final boolean transferForSignal(AbstractQueuedSynchronizer$Node node) {
        if (!compareAndSetWaitStatus(node, AbstractQueuedSynchronizer$Node.CONDITION, 0)) return false;
        AbstractQueuedSynchronizer$Node p = enq(node);
        int c = p.waitStatus;
        if (c > 0 || !compareAndSetWaitStatus(p, c, AbstractQueuedSynchronizer$Node.SIGNAL)) LockSupport.unpark(node.thread);
        return true;
    }
    
    final boolean transferAfterCancelledWait(AbstractQueuedSynchronizer$Node node) {
        if (compareAndSetWaitStatus(node, AbstractQueuedSynchronizer$Node.CONDITION, 0)) {
            enq(node);
            return true;
        }
        while (!isOnSyncQueue(node)) Thread.yield();
        return false;
    }
    
    final int fullyRelease(AbstractQueuedSynchronizer$Node node) {
        try {
            int savedState = getState();
            if (release(savedState)) return savedState;
        } catch (RuntimeException ex) {
            node.waitStatus = AbstractQueuedSynchronizer$Node.CANCELLED;
            throw ex;
        }
        node.waitStatus = AbstractQueuedSynchronizer$Node.CANCELLED;
        throw new IllegalMonitorStateException();
    }
    
    public final boolean owns(AbstractQueuedSynchronizer$ConditionObject condition) {
        if (condition == null) throw new NullPointerException();
        return condition.isOwnedBy(this);
    }
    
    public final boolean hasWaiters(AbstractQueuedSynchronizer$ConditionObject condition) {
        if (!owns(condition)) throw new IllegalArgumentException("Not owner");
        return condition.hasWaiters();
    }
    
    public final int getWaitQueueLength(AbstractQueuedSynchronizer$ConditionObject condition) {
        if (!owns(condition)) throw new IllegalArgumentException("Not owner");
        return condition.getWaitQueueLength();
    }
    
    public final Collection getWaitingThreads(AbstractQueuedSynchronizer$ConditionObject condition) {
        if (!owns(condition)) throw new IllegalArgumentException("Not owner");
        return condition.getWaitingThreads();
    }
    {
    }
    private static final Unsafe unsafe = Unsafe.getUnsafe();
    private static final long stateOffset;
    private static final long headOffset;
    private static final long tailOffset;
    private static final long waitStatusOffset;
    private static final long nextOffset;
    static {
        try {
            stateOffset = unsafe.objectFieldOffset(AbstractQueuedSynchronizer.class.getDeclaredField("state"));
            headOffset = unsafe.objectFieldOffset(AbstractQueuedSynchronizer.class.getDeclaredField("head"));
            tailOffset = unsafe.objectFieldOffset(AbstractQueuedSynchronizer.class.getDeclaredField("tail"));
            waitStatusOffset = unsafe.objectFieldOffset(AbstractQueuedSynchronizer.Node.class.getDeclaredField("waitStatus"));
            nextOffset = unsafe.objectFieldOffset(AbstractQueuedSynchronizer.Node.class.getDeclaredField("next"));
        } catch (Exception ex) {
            throw new Error(ex);
        }
    }
    
    private final boolean compareAndSetHead(AbstractQueuedSynchronizer$Node update) {
        return unsafe.compareAndSwapObject(this, headOffset, null, update);
    }
    
    private final boolean compareAndSetTail(AbstractQueuedSynchronizer$Node expect, AbstractQueuedSynchronizer$Node update) {
        return unsafe.compareAndSwapObject(this, tailOffset, expect, update);
    }
    
    private static final boolean compareAndSetWaitStatus(AbstractQueuedSynchronizer$Node node, int expect, int update) {
        return unsafe.compareAndSwapInt(node, waitStatusOffset, expect, update);
    }
    
    private static final boolean compareAndSetNext(AbstractQueuedSynchronizer$Node node, AbstractQueuedSynchronizer$Node expect, AbstractQueuedSynchronizer$Node update) {
        return unsafe.compareAndSwapObject(node, nextOffset, expect, update);
    }
}
