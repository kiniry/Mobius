package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

public class SynchronousQueue extends AbstractQueue implements BlockingQueue, java.io.Serializable {
    private static final long serialVersionUID = -3223113410248163686L;
    private final ReentrantLock qlock;
    private final SynchronousQueue$WaitQueue waitingProducers;
    private final SynchronousQueue$WaitQueue waitingConsumers;
    
    public SynchronousQueue() {
        this(false);
    }
    
    public SynchronousQueue(boolean fair) {
        
        if (fair) {
            qlock = new ReentrantLock(true);
            waitingProducers = new SynchronousQueue$FifoWaitQueue();
            waitingConsumers = new SynchronousQueue$FifoWaitQueue();
        } else {
            qlock = new ReentrantLock();
            waitingProducers = new SynchronousQueue$LifoWaitQueue();
            waitingConsumers = new SynchronousQueue$LifoWaitQueue();
        }
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    public void put(Object o) throws InterruptedException {
        if (o == null) throw new NullPointerException();
        final ReentrantLock qlock = this.qlock;
        for (; ; ) {
            SynchronousQueue$Node node;
            boolean mustWait;
            if (Thread.interrupted()) throw new InterruptedException();
            qlock.lock();
            try {
                node = waitingConsumers.deq();
                if (mustWait = (node == null)) node = waitingProducers.enq(o);
            } finally {
                qlock.unlock();
            }
            if (mustWait) {
                node.waitForTake();
                return;
            } else if (node.setItem(o)) return;
        }
    }
    
    public boolean offer(Object o, long timeout, TimeUnit unit) throws InterruptedException {
        if (o == null) throw new NullPointerException();
        long nanos = unit.toNanos(timeout);
        final ReentrantLock qlock = this.qlock;
        for (; ; ) {
            SynchronousQueue$Node node;
            boolean mustWait;
            if (Thread.interrupted()) throw new InterruptedException();
            qlock.lock();
            try {
                node = waitingConsumers.deq();
                if (mustWait = (node == null)) node = waitingProducers.enq(o);
            } finally {
                qlock.unlock();
            }
            if (mustWait) return node.waitForTake(nanos); else if (node.setItem(o)) return true;
        }
    }
    
    public Object take() throws InterruptedException {
        final ReentrantLock qlock = this.qlock;
        for (; ; ) {
            SynchronousQueue$Node node;
            boolean mustWait;
            if (Thread.interrupted()) throw new InterruptedException();
            qlock.lock();
            try {
                node = waitingProducers.deq();
                if (mustWait = (node == null)) node = waitingConsumers.enq(null);
            } finally {
                qlock.unlock();
            }
            if (mustWait) {
                Object x = node.waitForPut();
                return (Object)x;
            } else {
                Object x = node.getItem();
                if (x != null) return (Object)x;
            }
        }
    }
    
    public Object poll(long timeout, TimeUnit unit) throws InterruptedException {
        long nanos = unit.toNanos(timeout);
        final ReentrantLock qlock = this.qlock;
        for (; ; ) {
            SynchronousQueue$Node node;
            boolean mustWait;
            if (Thread.interrupted()) throw new InterruptedException();
            qlock.lock();
            try {
                node = waitingProducers.deq();
                if (mustWait = (node == null)) node = waitingConsumers.enq(null);
            } finally {
                qlock.unlock();
            }
            if (mustWait) {
                Object x = node.waitForPut(nanos);
                return (Object)x;
            } else {
                Object x = node.getItem();
                if (x != null) return (Object)x;
            }
        }
    }
    
    public boolean offer(Object o) {
        if (o == null) throw new NullPointerException();
        final ReentrantLock qlock = this.qlock;
        for (; ; ) {
            SynchronousQueue$Node node;
            qlock.lock();
            try {
                node = waitingConsumers.deq();
            } finally {
                qlock.unlock();
            }
            if (node == null) return false; else if (node.setItem(o)) return true;
        }
    }
    
    public Object poll() {
        final ReentrantLock qlock = this.qlock;
        for (; ; ) {
            SynchronousQueue$Node node;
            qlock.lock();
            try {
                node = waitingProducers.deq();
            } finally {
                qlock.unlock();
            }
            if (node == null) return null; else {
                Object x = node.getItem();
                if (x != null) return (Object)x;
            }
        }
    }
    
    public boolean isEmpty() {
        return true;
    }
    
    public int size() {
        return 0;
    }
    
    public int remainingCapacity() {
        return 0;
    }
    
    public void clear() {
    }
    
    public boolean contains(Object o) {
        return false;
    }
    
    public boolean remove(Object o) {
        return false;
    }
    
    public boolean containsAll(Collection c) {
        return c.isEmpty();
    }
    
    public boolean removeAll(Collection c) {
        return false;
    }
    
    public boolean retainAll(Collection c) {
        return false;
    }
    
    public Object peek() {
        return null;
    }
    {
    }
    
    public Iterator iterator() {
        return new SynchronousQueue$EmptyIterator();
    }
    
    public Object[] toArray() {
        return new Object[0];
    }
    
    public Object[] toArray(Object[] a) {
        if (a.length > 0) a[0] = null;
        return a;
    }
    
    public int drainTo(Collection c) {
        if (c == null) throw new NullPointerException();
        if (c == this) throw new IllegalArgumentException();
        int n = 0;
        Object e;
        while ((e = poll()) != null) {
            c.add(e);
            ++n;
        }
        return n;
    }
    
    public int drainTo(Collection c, int maxElements) {
        if (c == null) throw new NullPointerException();
        if (c == this) throw new IllegalArgumentException();
        int n = 0;
        Object e;
        while (n < maxElements && (e = poll()) != null) {
            c.add(e);
            ++n;
        }
        return n;
    }
}
