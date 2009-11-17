package java.util.concurrent.locks;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

public class AbstractQueuedSynchronizer$ConditionObject implements Condition, java.io.Serializable {
    /*synthetic*/ final AbstractQueuedSynchronizer this$0;
    private static final long serialVersionUID = 1173984872572414699L;
    private transient AbstractQueuedSynchronizer$Node firstWaiter;
    private transient AbstractQueuedSynchronizer$Node lastWaiter;
    
    public AbstractQueuedSynchronizer$ConditionObject(/*synthetic*/ final AbstractQueuedSynchronizer this$0) {
        this.this$0 = this$0;
        
    }
    
    private AbstractQueuedSynchronizer$Node addConditionWaiter() {
        AbstractQueuedSynchronizer$Node t = lastWaiter;
        if (t != null && t.waitStatus != AbstractQueuedSynchronizer$Node.CONDITION) {
            unlinkCancelledWaiters();
            t = lastWaiter;
        }
        AbstractQueuedSynchronizer$Node node = new AbstractQueuedSynchronizer$Node(Thread.currentThread(), AbstractQueuedSynchronizer$Node.CONDITION);
        if (t == null) firstWaiter = node; else t.nextWaiter = node;
        lastWaiter = node;
        return node;
    }
    
    private void doSignal(AbstractQueuedSynchronizer$Node first) {
        do {
            if ((firstWaiter = first.nextWaiter) == null) lastWaiter = null;
            first.nextWaiter = null;
        }         while (!this$0.transferForSignal(first) && (first = firstWaiter) != null);
    }
    
    private void doSignalAll(AbstractQueuedSynchronizer$Node first) {
        lastWaiter = firstWaiter = null;
        do {
            AbstractQueuedSynchronizer$Node next = first.nextWaiter;
            first.nextWaiter = null;
            this$0.transferForSignal(first);
            first = next;
        }         while (first != null);
    }
    
    public final void signal() {
        if (!this$0.isHeldExclusively()) throw new IllegalMonitorStateException();
        AbstractQueuedSynchronizer$Node first = firstWaiter;
        if (first != null) doSignal(first);
    }
    
    public final void signalAll() {
        if (!this$0.isHeldExclusively()) throw new IllegalMonitorStateException();
        AbstractQueuedSynchronizer$Node first = firstWaiter;
        if (first != null) doSignalAll(first);
    }
    
    private void unlinkCancelledWaiters() {
        AbstractQueuedSynchronizer$Node t = firstWaiter;
        AbstractQueuedSynchronizer$Node trail = null;
        while (t != null) {
            AbstractQueuedSynchronizer$Node next = t.nextWaiter;
            if (t.waitStatus != AbstractQueuedSynchronizer$Node.CONDITION) {
                t.nextWaiter = null;
                if (trail == null) firstWaiter = next; else trail.nextWaiter = next;
                if (next == null) lastWaiter = trail;
            } else trail = t;
            t = next;
        }
    }
    
    public final void awaitUninterruptibly() {
        AbstractQueuedSynchronizer$Node node = addConditionWaiter();
        int savedState = this$0.fullyRelease(node);
        boolean interrupted = false;
        while (!this$0.isOnSyncQueue(node)) {
            LockSupport.park();
            if (Thread.interrupted()) interrupted = true;
        }
        if (this$0.acquireQueued(node, savedState) || interrupted) AbstractQueuedSynchronizer.access$000();
    }
    private static final int REINTERRUPT = 1;
    private static final int THROW_IE = -1;
    
    private int checkInterruptWhileWaiting(AbstractQueuedSynchronizer$Node node) {
        return (Thread.interrupted()) ? ((this$0.transferAfterCancelledWait(node)) ? THROW_IE : REINTERRUPT) : 0;
    }
    
    private void reportInterruptAfterWait(int interruptMode) throws InterruptedException {
        if (interruptMode == THROW_IE) throw new InterruptedException(); else if (interruptMode == REINTERRUPT) Thread.currentThread().interrupt();
    }
    
    public final void await() throws InterruptedException {
        if (Thread.interrupted()) throw new InterruptedException();
        AbstractQueuedSynchronizer$Node node = addConditionWaiter();
        int savedState = this$0.fullyRelease(node);
        int interruptMode = 0;
        while (!this$0.isOnSyncQueue(node)) {
            LockSupport.park();
            if ((interruptMode = checkInterruptWhileWaiting(node)) != 0) break;
        }
        if (this$0.acquireQueued(node, savedState) && interruptMode != THROW_IE) interruptMode = REINTERRUPT;
        if (node.nextWaiter != null) unlinkCancelledWaiters();
        if (interruptMode != 0) reportInterruptAfterWait(interruptMode);
    }
    
    public final long awaitNanos(long nanosTimeout) throws InterruptedException {
        if (Thread.interrupted()) throw new InterruptedException();
        AbstractQueuedSynchronizer$Node node = addConditionWaiter();
        int savedState = this$0.fullyRelease(node);
        long lastTime = System.nanoTime();
        int interruptMode = 0;
        while (!this$0.isOnSyncQueue(node)) {
            if (nanosTimeout <= 0L) {
                this$0.transferAfterCancelledWait(node);
                break;
            }
            LockSupport.parkNanos(nanosTimeout);
            if ((interruptMode = checkInterruptWhileWaiting(node)) != 0) break;
            long now = System.nanoTime();
            nanosTimeout -= now - lastTime;
            lastTime = now;
        }
        if (this$0.acquireQueued(node, savedState) && interruptMode != THROW_IE) interruptMode = REINTERRUPT;
        if (node.nextWaiter != null) unlinkCancelledWaiters();
        if (interruptMode != 0) reportInterruptAfterWait(interruptMode);
        return nanosTimeout - (System.nanoTime() - lastTime);
    }
    
    public final boolean awaitUntil(Date deadline) throws InterruptedException {
        if (deadline == null) throw new NullPointerException();
        long abstime = deadline.getTime();
        if (Thread.interrupted()) throw new InterruptedException();
        AbstractQueuedSynchronizer$Node node = addConditionWaiter();
        int savedState = this$0.fullyRelease(node);
        boolean timedout = false;
        int interruptMode = 0;
        while (!this$0.isOnSyncQueue(node)) {
            if (System.currentTimeMillis() > abstime) {
                timedout = this$0.transferAfterCancelledWait(node);
                break;
            }
            LockSupport.parkUntil(abstime);
            if ((interruptMode = checkInterruptWhileWaiting(node)) != 0) break;
        }
        if (this$0.acquireQueued(node, savedState) && interruptMode != THROW_IE) interruptMode = REINTERRUPT;
        if (node.nextWaiter != null) unlinkCancelledWaiters();
        if (interruptMode != 0) reportInterruptAfterWait(interruptMode);
        return !timedout;
    }
    
    public final boolean await(long time, TimeUnit unit) throws InterruptedException {
        if (unit == null) throw new NullPointerException();
        long nanosTimeout = unit.toNanos(time);
        if (Thread.interrupted()) throw new InterruptedException();
        AbstractQueuedSynchronizer$Node node = addConditionWaiter();
        int savedState = this$0.fullyRelease(node);
        long lastTime = System.nanoTime();
        boolean timedout = false;
        int interruptMode = 0;
        while (!this$0.isOnSyncQueue(node)) {
            if (nanosTimeout <= 0L) {
                timedout = this$0.transferAfterCancelledWait(node);
                break;
            }
            LockSupport.parkNanos(nanosTimeout);
            if ((interruptMode = checkInterruptWhileWaiting(node)) != 0) break;
            long now = System.nanoTime();
            nanosTimeout -= now - lastTime;
            lastTime = now;
        }
        if (this$0.acquireQueued(node, savedState) && interruptMode != THROW_IE) interruptMode = REINTERRUPT;
        if (node.nextWaiter != null) unlinkCancelledWaiters();
        if (interruptMode != 0) reportInterruptAfterWait(interruptMode);
        return !timedout;
    }
    
    final boolean isOwnedBy(AbstractQueuedSynchronizer sync) {
        return sync == this$0;
    }
    
    protected final boolean hasWaiters() {
        if (!this$0.isHeldExclusively()) throw new IllegalMonitorStateException();
        for (AbstractQueuedSynchronizer$Node w = firstWaiter; w != null; w = w.nextWaiter) {
            if (w.waitStatus == AbstractQueuedSynchronizer$Node.CONDITION) return true;
        }
        return false;
    }
    
    protected final int getWaitQueueLength() {
        if (!this$0.isHeldExclusively()) throw new IllegalMonitorStateException();
        int n = 0;
        for (AbstractQueuedSynchronizer$Node w = firstWaiter; w != null; w = w.nextWaiter) {
            if (w.waitStatus == AbstractQueuedSynchronizer$Node.CONDITION) ++n;
        }
        return n;
    }
    
    protected final Collection getWaitingThreads() {
        if (!this$0.isHeldExclusively()) throw new IllegalMonitorStateException();
        ArrayList list = new ArrayList();
        for (AbstractQueuedSynchronizer$Node w = firstWaiter; w != null; w = w.nextWaiter) {
            if (w.waitStatus == AbstractQueuedSynchronizer$Node.CONDITION) {
                Thread t = w.thread;
                if (t != null) list.add(t);
            }
        }
        return list;
    }
}
