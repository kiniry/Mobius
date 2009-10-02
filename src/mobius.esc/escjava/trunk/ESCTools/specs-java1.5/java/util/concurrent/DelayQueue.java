package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

public class DelayQueue extends AbstractQueue implements BlockingQueue {
    
    /*synthetic*/ static ReentrantLock access$000(DelayQueue x0) {
        return x0.lock;
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !DelayQueue.class.desiredAssertionStatus();
    private final transient ReentrantLock lock = new ReentrantLock();
    private final transient Condition available = lock.newCondition();
    private final PriorityQueue q = new PriorityQueue();
    
    public DelayQueue() {
        
    }
    
    public DelayQueue(Collection c) {
        
        this.addAll(c);
    }
    
    public boolean offer(Delayed o) {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            Delayed first = (Delayed)q.peek();
            q.offer(o);
            if (first == null || o.compareTo(first) < 0) available.signalAll();
            return true;
        } finally {
            lock.unlock();
        }
    }
    
    public void put(Delayed o) {
        offer(o);
    }
    
    public boolean offer(Delayed o, long timeout, TimeUnit unit) {
        return offer(o);
    }
    
    public boolean add(Delayed o) {
        return offer(o);
    }
    
    public Delayed take() throws InterruptedException {
        final ReentrantLock lock = this.lock;
        lock.lockInterruptibly();
        try {
            for (; ; ) {
                Delayed first = (Delayed)q.peek();
                if (first == null) {
                    available.await();
                } else {
                    long delay = first.getDelay(TimeUnit.NANOSECONDS);
                    if (delay > 0) {
                        long tl = available.awaitNanos(delay);
                    } else {
                        Delayed x = (Delayed)q.poll();
                        if (!$assertionsDisabled && !(x != null)) throw new AssertionError();
                        if (q.size() != 0) available.signalAll();
                        return x;
                    }
                }
            }
        } finally {
            lock.unlock();
        }
    }
    
    public Delayed poll(long timeout, TimeUnit unit) throws InterruptedException {
        final ReentrantLock lock = this.lock;
        lock.lockInterruptibly();
        long nanos = unit.toNanos(timeout);
        try {
            for (; ; ) {
                Delayed first = (Delayed)q.peek();
                if (first == null) {
                    if (nanos <= 0) return null; else nanos = available.awaitNanos(nanos);
                } else {
                    long delay = first.getDelay(TimeUnit.NANOSECONDS);
                    if (delay > 0) {
                        if (nanos <= 0) return null;
                        if (delay > nanos) delay = nanos;
                        long timeLeft = available.awaitNanos(delay);
                        nanos -= delay - timeLeft;
                    } else {
                        Delayed x = (Delayed)q.poll();
                        if (!$assertionsDisabled && !(x != null)) throw new AssertionError();
                        if (q.size() != 0) available.signalAll();
                        return x;
                    }
                }
            }
        } finally {
            lock.unlock();
        }
    }
    
    public Delayed poll() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            Delayed first = (Delayed)q.peek();
            if (first == null || first.getDelay(TimeUnit.NANOSECONDS) > 0) return null; else {
                Delayed x = (Delayed)q.poll();
                if (!$assertionsDisabled && !(x != null)) throw new AssertionError();
                if (q.size() != 0) available.signalAll();
                return x;
            }
        } finally {
            lock.unlock();
        }
    }
    
    public Delayed peek() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return (Delayed)q.peek();
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
    
    public int drainTo(Collection c) {
        if (c == null) throw new NullPointerException();
        if (c == this) throw new IllegalArgumentException();
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            int n = 0;
            for (; ; ) {
                Delayed first = (Delayed)q.peek();
                if (first == null || first.getDelay(TimeUnit.NANOSECONDS) > 0) break;
                c.add(q.poll());
                ++n;
            }
            if (n > 0) available.signalAll();
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
            while (n < maxElements) {
                Delayed first = (Delayed)q.peek();
                if (first == null || first.getDelay(TimeUnit.NANOSECONDS) > 0) break;
                c.add(q.poll());
                ++n;
            }
            if (n > 0) available.signalAll();
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
    
    public int remainingCapacity() {
        return Integer.MAX_VALUE;
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
    
    public Object[] toArray(Object[] array) {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return q.toArray(array);
        } finally {
            lock.unlock();
        }
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
    
    public Iterator iterator() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return new DelayQueue$Itr(this, q.iterator());
        } finally {
            lock.unlock();
        }
    }
    {
    }
    
    /*synthetic*/ public boolean add(Object x0) {
        return this.add((Delayed)x0);
    }
    
    /*synthetic public Object peek() {
        return this.peek();
    } */
    
    /*synthetic public Object poll() {
        return this.poll();
    } */
    
    /*synthetic*/ public boolean offer(Object x0) {
        return this.offer((Delayed)x0);
    }
    
    /*synthetic*/ public void put(Object x0) throws InterruptedException {
        this.put((Delayed)x0);
    }
    
    /*synthetic public Object take() throws InterruptedException {
        return this.take();
    }*/
    
    /*synthetic public Object poll(long x0, TimeUnit x1) throws InterruptedException {
        return this.poll(x0, x1);
    } */
    
    /*synthetic*/ public boolean offer(Object x0, long x1, TimeUnit x2) throws InterruptedException {
        return this.offer((Delayed)x0, x1, x2);
    }
}
