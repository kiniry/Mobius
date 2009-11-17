package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

public class ArrayBlockingQueue extends AbstractQueue implements BlockingQueue, java.io.Serializable {
    
    /*synthetic*/ static ReentrantLock access$400(ArrayBlockingQueue x0) {
        return x0.lock;
    }
    
    /*synthetic*/ static int access$300(ArrayBlockingQueue x0) {
        return x0.putIndex;
    }
    
    /*synthetic*/ static Object[] access$200(ArrayBlockingQueue x0) {
        return x0.items;
    }
    
    /*synthetic*/ static int access$100(ArrayBlockingQueue x0) {
        return x0.takeIndex;
    }
    
    /*synthetic*/ static int access$000(ArrayBlockingQueue x0) {
        return x0.count;
    }
    private static final long serialVersionUID = -817911632652898426L;
    private final Object[] items;
    private transient int takeIndex;
    private transient int putIndex;
    private int count;
    private final ReentrantLock lock;
    private final Condition notEmpty;
    private final Condition notFull;
    
    final int inc(int i) {
        return (++i == items.length) ? 0 : i;
    }
    
    private void insert(Object x) {
        items[putIndex] = x;
        putIndex = inc(putIndex);
        ++count;
        notEmpty.signal();
    }
    
    private Object extract() {
        final Object[] items = this.items;
        Object x = items[takeIndex];
        items[takeIndex] = null;
        takeIndex = inc(takeIndex);
        --count;
        notFull.signal();
        return x;
    }
    
    void removeAt(int i) {
        final Object[] items = this.items;
        if (i == takeIndex) {
            items[takeIndex] = null;
            takeIndex = inc(takeIndex);
        } else {
            for (; ; ) {
                int nexti = inc(i);
                if (nexti != putIndex) {
                    items[i] = items[nexti];
                    i = nexti;
                } else {
                    items[i] = null;
                    putIndex = i;
                    break;
                }
            }
        }
        --count;
        notFull.signal();
    }
    
    public ArrayBlockingQueue(int capacity) {
        this(capacity, false);
    }
    
    public ArrayBlockingQueue(int capacity, boolean fair) {
        
        if (capacity <= 0) throw new IllegalArgumentException();
        this.items = (Object[])new Object[capacity];
        lock = new ReentrantLock(fair);
        notEmpty = lock.newCondition();
        notFull = lock.newCondition();
    }
    
    public ArrayBlockingQueue(int capacity, boolean fair, Collection c) {
        this(capacity, fair);
        if (capacity < c.size()) throw new IllegalArgumentException();
        for (Iterator it = c.iterator(); it.hasNext(); ) add(it.next());
    }
    
    public boolean offer(Object o) {
        if (o == null) throw new NullPointerException();
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            if (count == items.length) return false; else {
                insert(o);
                return true;
            }
        } finally {
            lock.unlock();
        }
    }
    
    public boolean offer(Object o, long timeout, TimeUnit unit) throws InterruptedException {
        if (o == null) throw new NullPointerException();
        final ReentrantLock lock = this.lock;
        lock.lockInterruptibly();
        try {
            long nanos = unit.toNanos(timeout);
            for (; ; ) {
                if (count != items.length) {
                    insert(o);
                    return true;
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
            lock.unlock();
        }
    }
    
    public Object poll() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            if (count == 0) return null;
            Object x = extract();
            return x;
        } finally {
            lock.unlock();
        }
    }
    
    public Object poll(long timeout, TimeUnit unit) throws InterruptedException {
        final ReentrantLock lock = this.lock;
        lock.lockInterruptibly();
        try {
            long nanos = unit.toNanos(timeout);
            for (; ; ) {
                if (count != 0) {
                    Object x = extract();
                    return x;
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
            lock.unlock();
        }
    }
    
    public boolean remove(Object o) {
        if (o == null) return false;
        final Object[] items = this.items;
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            int i = takeIndex;
            int k = 0;
            for (; ; ) {
                if (k++ >= count) return false;
                if (o.equals(items[i])) {
                    removeAt(i);
                    return true;
                }
                i = inc(i);
            }
        } finally {
            lock.unlock();
        }
    }
    
    public Object peek() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return (count == 0) ? null : items[takeIndex];
        } finally {
            lock.unlock();
        }
    }
    
    public Object take() throws InterruptedException {
        final ReentrantLock lock = this.lock;
        lock.lockInterruptibly();
        try {
            try {
                while (count == 0) notEmpty.await();
            } catch (InterruptedException ie) {
                notEmpty.signal();
                throw ie;
            }
            Object x = extract();
            return x;
        } finally {
            lock.unlock();
        }
    }
    
    public void put(Object o) throws InterruptedException {
        if (o == null) throw new NullPointerException();
        final Object[] items = this.items;
        final ReentrantLock lock = this.lock;
        lock.lockInterruptibly();
        try {
            try {
                while (count == items.length) notFull.await();
            } catch (InterruptedException ie) {
                notFull.signal();
                throw ie;
            }
            insert(o);
        } finally {
            lock.unlock();
        }
    }
    
    public int size() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return count;
        } finally {
            lock.unlock();
        }
    }
    
    public int remainingCapacity() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return items.length - count;
        } finally {
            lock.unlock();
        }
    }
    
    public boolean contains(Object o) {
        if (o == null) return false;
        final Object[] items = this.items;
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            int i = takeIndex;
            int k = 0;
            while (k++ < count) {
                if (o.equals(items[i])) return true;
                i = inc(i);
            }
            return false;
        } finally {
            lock.unlock();
        }
    }
    
    public Object[] toArray() {
        final Object[] items = this.items;
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            Object[] a = new Object[count];
            int k = 0;
            int i = takeIndex;
            while (k < count) {
                a[k++] = items[i];
                i = inc(i);
            }
            return a;
        } finally {
            lock.unlock();
        }
    }
    
    public Object[] toArray(Object[] a) {
        final Object[] items = this.items;
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            if (a.length < count) a = (Object[])(Object[])java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), count);
            int k = 0;
            int i = takeIndex;
            while (k < count) {
                a[k++] = (Object)items[i];
                i = inc(i);
            }
            if (a.length > count) a[count] = null;
            return a;
        } finally {
            lock.unlock();
        }
    }
    
    public String toString() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return super.toString();
        } finally {
            lock.unlock();
        }
    }
    
    public void clear() {
        final Object[] items = this.items;
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            int i = takeIndex;
            int k = count;
            while (k-- > 0) {
                items[i] = null;
                i = inc(i);
            }
            count = 0;
            putIndex = 0;
            takeIndex = 0;
            notFull.signalAll();
        } finally {
            lock.unlock();
        }
    }
    
    public int drainTo(Collection c) {
        if (c == null) throw new NullPointerException();
        if (c == this) throw new IllegalArgumentException();
        final Object[] items = this.items;
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            int i = takeIndex;
            int n = 0;
            int max = count;
            while (n < max) {
                c.add(items[i]);
                items[i] = null;
                i = inc(i);
                ++n;
            }
            if (n > 0) {
                count = 0;
                putIndex = 0;
                takeIndex = 0;
                notFull.signalAll();
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
        final Object[] items = this.items;
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            int i = takeIndex;
            int n = 0;
            int sz = count;
            int max = (maxElements < count) ? maxElements : count;
            while (n < max) {
                c.add(items[i]);
                items[i] = null;
                i = inc(i);
                ++n;
            }
            if (n > 0) {
                count -= n;
                takeIndex = i;
                notFull.signalAll();
            }
            return n;
        } finally {
            lock.unlock();
        }
    }
    
    public Iterator iterator() {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
            return new ArrayBlockingQueue$Itr(this);
        } finally {
            lock.unlock();
        }
    }
    {
    }
}
