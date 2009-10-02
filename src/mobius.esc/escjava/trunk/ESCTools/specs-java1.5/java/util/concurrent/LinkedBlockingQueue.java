package java.util.concurrent;

import java.util.concurrent.atomic.*;
import java.util.concurrent.locks.*;
import java.util.*;

public class LinkedBlockingQueue extends AbstractQueue implements BlockingQueue, java.io.Serializable {
    
    /*synthetic*/ static Condition access$600(LinkedBlockingQueue x0) {
        return x0.notFull;
    }
    
    /*synthetic*/ static int access$500(LinkedBlockingQueue x0) {
        return x0.capacity;
    }
    
    /*synthetic*/ static AtomicInteger access$400(LinkedBlockingQueue x0) {
        return x0.count;
    }
    
    /*synthetic*/ static LinkedBlockingQueue$Node access$302(LinkedBlockingQueue x0, LinkedBlockingQueue$Node x1) {
        return x0.last = x1;
    }
    
    /*synthetic*/ static LinkedBlockingQueue$Node access$300(LinkedBlockingQueue x0) {
        return x0.last;
    }
    
    /*synthetic*/ static LinkedBlockingQueue$Node access$200(LinkedBlockingQueue x0) {
        return x0.head;
    }
    
    /*synthetic*/ static ReentrantLock access$100(LinkedBlockingQueue x0) {
        return x0.takeLock;
    }
    
    /*synthetic*/ static ReentrantLock access$000(LinkedBlockingQueue x0) {
        return x0.putLock;
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !LinkedBlockingQueue.class.desiredAssertionStatus();
    private static final long serialVersionUID = -6903933977591709194L;
    {
    }
    private final int capacity;
    private final AtomicInteger count = new AtomicInteger(0);
    private transient LinkedBlockingQueue$Node head;
    private transient LinkedBlockingQueue$Node last;
    private final ReentrantLock takeLock = new ReentrantLock();
    private final Condition notEmpty = takeLock.newCondition();
    private final ReentrantLock putLock = new ReentrantLock();
    private final Condition notFull = putLock.newCondition();
    
    private void signalNotEmpty() {
        final ReentrantLock takeLock = this.takeLock;
        takeLock.lock();
        try {
            notEmpty.signal();
        } finally {
            takeLock.unlock();
        }
    }
    
    private void signalNotFull() {
        final ReentrantLock putLock = this.putLock;
        putLock.lock();
        try {
            notFull.signal();
        } finally {
            putLock.unlock();
        }
    }
    
    private void insert(Object x) {
        last = last.next = new LinkedBlockingQueue$Node(x);
    }
    
    private Object extract() {
        LinkedBlockingQueue$Node first = head.next;
        head = first;
        Object x = first.item;
        first.item = null;
        return x;
    }
    
    private void fullyLock() {
        putLock.lock();
        takeLock.lock();
    }
    
    private void fullyUnlock() {
        takeLock.unlock();
        putLock.unlock();
    }
    
    public LinkedBlockingQueue() {
        this(Integer.MAX_VALUE);
    }
    
    public LinkedBlockingQueue(int capacity) {
        
        if (capacity <= 0) throw new IllegalArgumentException();
        this.capacity = capacity;
        last = head = new LinkedBlockingQueue$Node(null);
    }
    
    public LinkedBlockingQueue(Collection c) {
        this(Integer.MAX_VALUE);
        for (Iterator i$ = c.iterator(); i$.hasNext(); ) {
            Object e = (Object)i$.next();
            add(e);
        }
    }
    
    public int size() {
        return count.get();
    }
    
    public int remainingCapacity() {
        return capacity - count.get();
    }
    
    public void put(Object o) throws InterruptedException {
        if (o == null) throw new NullPointerException();
        int c = -1;
        final ReentrantLock putLock = this.putLock;
        final AtomicInteger count = this.count;
        putLock.lockInterruptibly();
        try {
            try {
                while (count.get() == capacity) notFull.await();
            } catch (InterruptedException ie) {
                notFull.signal();
                throw ie;
            }
            insert(o);
            c = count.getAndIncrement();
            if (c + 1 < capacity) notFull.signal();
        } finally {
            putLock.unlock();
        }
        if (c == 0) signalNotEmpty();
    }
    
    public boolean offer(Object o, long timeout, TimeUnit unit) throws InterruptedException {
        if (o == null) throw new NullPointerException();
        long nanos = unit.toNanos(timeout);
        int c = -1;
        final ReentrantLock putLock = this.putLock;
        final AtomicInteger count = this.count;
        putLock.lockInterruptibly();
        try {
            for (; ; ) {
                if (count.get() < capacity) {
                    insert(o);
                    c = count.getAndIncrement();
                    if (c + 1 < capacity) notFull.signal();
                    break;
                }
                if (nanos <= 0) return false;
                try {
                    nanos = notFull.awaitNanos(nanos);
                } catch (InterruptedException ie) {
                    notFull.signal();
                    throw ie;
                }
            }
        } finally {
            putLock.unlock();
        }
        if (c == 0) signalNotEmpty();
        return true;
    }
    
    public boolean offer(Object o) {
        if (o == null) throw new NullPointerException();
        final AtomicInteger count = this.count;
        if (count.get() == capacity) return false;
        int c = -1;
        final ReentrantLock putLock = this.putLock;
        putLock.lock();
        try {
            if (count.get() < capacity) {
                insert(o);
                c = count.getAndIncrement();
                if (c + 1 < capacity) notFull.signal();
            }
        } finally {
            putLock.unlock();
        }
        if (c == 0) signalNotEmpty();
        return c >= 0;
    }
    
    public Object take() throws InterruptedException {
        Object x;
        int c = -1;
        final AtomicInteger count = this.count;
        final ReentrantLock takeLock = this.takeLock;
        takeLock.lockInterruptibly();
        try {
            try {
                while (count.get() == 0) notEmpty.await();
            } catch (InterruptedException ie) {
                notEmpty.signal();
                throw ie;
            }
            x = extract();
            c = count.getAndDecrement();
            if (c > 1) notEmpty.signal();
        } finally {
            takeLock.unlock();
        }
        if (c == capacity) signalNotFull();
        return x;
    }
    
    public Object poll(long timeout, TimeUnit unit) throws InterruptedException {
        Object x = null;
        int c = -1;
        long nanos = unit.toNanos(timeout);
        final AtomicInteger count = this.count;
        final ReentrantLock takeLock = this.takeLock;
        takeLock.lockInterruptibly();
        try {
            for (; ; ) {
                if (count.get() > 0) {
                    x = extract();
                    c = count.getAndDecrement();
                    if (c > 1) notEmpty.signal();
                    break;
                }
                if (nanos <= 0) return null;
                try {
                    nanos = notEmpty.awaitNanos(nanos);
                } catch (InterruptedException ie) {
                    notEmpty.signal();
                    throw ie;
                }
            }
        } finally {
            takeLock.unlock();
        }
        if (c == capacity) signalNotFull();
        return x;
    }
    
    public Object poll() {
        final AtomicInteger count = this.count;
        if (count.get() == 0) return null;
        Object x = null;
        int c = -1;
        final ReentrantLock takeLock = this.takeLock;
        takeLock.lock();
        try {
            if (count.get() > 0) {
                x = extract();
                c = count.getAndDecrement();
                if (c > 1) notEmpty.signal();
            }
        } finally {
            takeLock.unlock();
        }
        if (c == capacity) signalNotFull();
        return x;
    }
    
    public Object peek() {
        if (count.get() == 0) return null;
        final ReentrantLock takeLock = this.takeLock;
        takeLock.lock();
        try {
            LinkedBlockingQueue$Node first = head.next;
            if (first == null) return null; else return first.item;
        } finally {
            takeLock.unlock();
        }
    }
    
    public boolean remove(Object o) {
        if (o == null) return false;
        boolean removed = false;
        fullyLock();
        try {
            LinkedBlockingQueue$Node trail = head;
            LinkedBlockingQueue$Node p = head.next;
            while (p != null) {
                if (o.equals(p.item)) {
                    removed = true;
                    break;
                }
                trail = p;
                p = p.next;
            }
            if (removed) {
                p.item = null;
                trail.next = p.next;
                if (last == p) last = trail;
                if (count.getAndDecrement() == capacity) notFull.signalAll();
            }
        } finally {
            fullyUnlock();
        }
        return removed;
    }
    
    public Object[] toArray() {
        fullyLock();
        try {
            int size = count.get();
            Object[] a = new Object[size];
            int k = 0;
            for (LinkedBlockingQueue$Node p = head.next; p != null; p = p.next) a[k++] = p.item;
            return a;
        } finally {
            fullyUnlock();
        }
    }
    
    public Object[] toArray(Object[] a) {
        fullyLock();
        try {
            int size = count.get();
            if (a.length < size) a = (Object[])(Object[])java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), size);
            int k = 0;
            for (LinkedBlockingQueue$Node p = head.next; p != null; p = p.next) a[k++] = (Object)p.item;
            if (a.length > k) a[k] = null;
            return a;
        } finally {
            fullyUnlock();
        }
    }
    
    public String toString() {
        fullyLock();
        try {
            return super.toString();
        } finally {
            fullyUnlock();
        }
    }
    
    public void clear() {
        fullyLock();
        try {
            head.next = null;
            if (!$assertionsDisabled && !(head.item == null)) throw new AssertionError();
            last = head;
            if (count.getAndSet(0) == capacity) notFull.signalAll();
        } finally {
            fullyUnlock();
        }
    }
    
    public int drainTo(Collection c) {
        if (c == null) throw new NullPointerException();
        if (c == this) throw new IllegalArgumentException();
        LinkedBlockingQueue$Node first;
        fullyLock();
        try {
            first = head.next;
            head.next = null;
            if (!$assertionsDisabled && !(head.item == null)) throw new AssertionError();
            last = head;
            if (count.getAndSet(0) == capacity) notFull.signalAll();
        } finally {
            fullyUnlock();
        }
        int n = 0;
        for (LinkedBlockingQueue$Node p = first; p != null; p = p.next) {
            c.add(p.item);
            p.item = null;
            ++n;
        }
        return n;
    }
    
    public int drainTo(Collection c, int maxElements) {
        if (c == null) throw new NullPointerException();
        if (c == this) throw new IllegalArgumentException();
        fullyLock();
        try {
            int n = 0;
            LinkedBlockingQueue$Node p = head.next;
            while (p != null && n < maxElements) {
                c.add(p.item);
                p.item = null;
                p = p.next;
                ++n;
            }
            if (n != 0) {
                head.next = p;
                if (!$assertionsDisabled && !(head.item == null)) throw new AssertionError();
                if (p == null) last = head;
                if (count.getAndAdd(-n) == capacity) notFull.signalAll();
            }
            return n;
        } finally {
            fullyUnlock();
        }
    }
    
    public Iterator iterator() {
        return new LinkedBlockingQueue$Itr(this);
    }
    {
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        fullyLock();
        try {
            s.defaultWriteObject();
            for (LinkedBlockingQueue$Node p = head.next; p != null; p = p.next) s.writeObject(p.item);
            s.writeObject(null);
        } finally {
            fullyUnlock();
        }
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        count.set(0);
        last = head = new LinkedBlockingQueue$Node(null);
        for (; ; ) {
            Object item = (Object)s.readObject();
            if (item == null) break;
            add(item);
        }
    }
}
