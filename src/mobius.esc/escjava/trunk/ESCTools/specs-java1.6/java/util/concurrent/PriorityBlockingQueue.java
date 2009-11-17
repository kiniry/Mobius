package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

public class PriorityBlockingQueue extends AbstractQueue implements BlockingQueue, java.io.Serializable {
    
    /*synthetic*/ static ReentrantLock access$000(PriorityBlockingQueue x0) {
        return x0.lock;
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !PriorityBlockingQueue.class.desiredAssertionStatus();
    private static final long serialVersionUID = 5595510919245408276L;
    private final PriorityQueue q;
    private final ReentrantLock lock = new ReentrantLock(true);
    private final Condition notEmpty = lock.newCondition();
    
    public PriorityBlockingQueue() {
        
        q = new PriorityQueue();
    }
    
    public PriorityBlockingQueue(int initialCapacity) {
        
        q = new PriorityQueue(initialCapacity, null);
    }
    
    public PriorityBlockingQueue(int initialCapacity, Comparator comparator) {
        
        q = new PriorityQueue(initialCapacity, comparator);
    }
    
    public PriorityBlockingQueue(Collection c) {
        
        q = new PriorityQueue(c);
    }
    
    public boolean add(Object o) {
        return super.add(o);
    }
    
    public Comparator comparator() {
        return q.comparator();
    }
    
    public boolean offer(Object o) {
        if (o == null) throw new NullPointerException();
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            boolean ok = q.offer(o);
            if (!$assertionsDisabled && !ok) throw new AssertionError();
            notEmpty.signal();
            return true;
        } finally {
            lock.unlock();
        }
    }
    
    public void put(Object o) {
        offer(o);
    }
    
    public boolean offer(Object o, long timeout, TimeUnit unit) {
        return offer(o);
    }
    
    public Object take() throws InterruptedException {
        final ReentrantLock lock = this.lock;
        lock.lockInterruptibly();
        try {
            try {
                while (q.size() == 0) notEmpty.await();
            } catch (InterruptedException ie) {
                notEmpty.signal();
                throw ie;
            }
            Object x = q.poll();
            if (!$assertionsDisabled && !(x != null)) throw new AssertionError();
            return x;
        } finally {
            lock.unlock();
        }
    }
    
    public Object poll() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return q.poll();
        } finally {
            lock.unlock();
        }
    }
    
    public Object poll(long timeout, TimeUnit unit) throws InterruptedException {
        long nanos = unit.toNanos(timeout);
        final ReentrantLock lock = this.lock;
        lock.lockInterruptibly();
        try {
            for (; ; ) {
                Object x = q.poll();
                if (x != null) return x;
                if (nanos <= 0) return null;
                try {
                    nanos = notEmpty.awaitNanos(nanos);
                } catch (InterruptedException ie) {
                    notEmpty.signal();
                    throw ie;
                }
            }
        } finally {
            lock.unlock();
        }
    }
    
    public Object peek() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return q.peek();
        } finally {
            lock.unlock();
        }
    }
    
    public int size() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return q.size();
        } finally {
            lock.unlock();
        }
    }
    
    public int remainingCapacity() {
        return Integer.MAX_VALUE;
    }
    
    public boolean remove(Object o) {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return q.remove(o);
        } finally {
            lock.unlock();
        }
    }
    
    public boolean contains(Object o) {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return q.contains(o);
        } finally {
            lock.unlock();
        }
    }
    
    public Object[] toArray() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return q.toArray();
        } finally {
            lock.unlock();
        }
    }
    
    public String toString() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return q.toString();
        } finally {
            lock.unlock();
        }
    }
    
    public int drainTo(Collection c) {
        if (c == null) throw new NullPointerException();
        if (c == this) throw new IllegalArgumentException();
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            int n = 0;
            Object e;
            while ((e = q.poll()) != null) {
                c.add(e);
                ++n;
            }
            return n;
        } finally {
            lock.unlock();
        }
    }
    
    public int drainTo(Collection c, int maxElements) {
        if (c == null) throw new NullPointerException();
        if (c == this) throw new IllegalArgumentException();
        if (maxElements <= 0) return 0;
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            int n = 0;
            Object e;
            while (n < maxElements && (e = q.poll()) != null) {
                c.add(e);
                ++n;
            }
            return n;
        } finally {
            lock.unlock();
        }
    }
    
    public void clear() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            q.clear();
        } finally {
            lock.unlock();
        }
    }
    
    public Object[] toArray(Object[] a) {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return q.toArray(a);
        } finally {
            lock.unlock();
        }
    }
    
    public Iterator iterator() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return new PriorityBlockingQueue$Itr(this, q.iterator());
        } finally {
            lock.unlock();
        }
    }
    {
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        lock.lock();
        try {
            s.defaultWriteObject();
        } finally {
            lock.unlock();
        }
    }
}
