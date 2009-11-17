package java.util.concurrent.atomic;

import sun.misc.Unsafe;

public class AtomicInteger extends Number implements java.io.Serializable {
    private static final long serialVersionUID = 6214790243416807050L;
    private static final Unsafe unsafe = Unsafe.getUnsafe();
    private static final long valueOffset;
    static {
        try {
            valueOffset = unsafe.objectFieldOffset(AtomicInteger.class.getDeclaredField("value"));
        } catch (Exception ex) {
            throw new Error(ex);
        }
    }
    private volatile int value;
    
    public AtomicInteger(int initialValue) {
        
        value = initialValue;
    }
    
    public AtomicInteger() {
        
    }
    
    public final int get() {
        return value;
    }
    
    public final void set(int newValue) {
        value = newValue;
    }
    
    public final int getAndSet(int newValue) {
        for (; ; ) {
            int current = get();
            if (compareAndSet(current, newValue)) return current;
        }
    }
    
    public final boolean compareAndSet(int expect, int update) {
        return unsafe.compareAndSwapInt(this, valueOffset, expect, update);
    }
    
    public final boolean weakCompareAndSet(int expect, int update) {
        return unsafe.compareAndSwapInt(this, valueOffset, expect, update);
    }
    
    public final int getAndIncrement() {
        for (; ; ) {
            int current = get();
            int next = current + 1;
            if (compareAndSet(current, next)) return current;
        }
    }
    
    public final int getAndDecrement() {
        for (; ; ) {
            int current = get();
            int next = current - 1;
            if (compareAndSet(current, next)) return current;
        }
    }
    
    public final int getAndAdd(int delta) {
        for (; ; ) {
            int current = get();
            int next = current + delta;
            if (compareAndSet(current, next)) return current;
        }
    }
    
    public final int incrementAndGet() {
        for (; ; ) {
            int current = get();
            int next = current + 1;
            if (compareAndSet(current, next)) return next;
        }
    }
    
    public final int decrementAndGet() {
        for (; ; ) {
            int current = get();
            int next = current - 1;
            if (compareAndSet(current, next)) return next;
        }
    }
    
    public final int addAndGet(int delta) {
        for (; ; ) {
            int current = get();
            int next = current + delta;
            if (compareAndSet(current, next)) return next;
        }
    }
    
    public String toString() {
        return Integer.toString(get());
    }
    
    public int intValue() {
        return get();
    }
    
    public long longValue() {
        return (long)get();
    }
    
    public float floatValue() {
        return (float)get();
    }
    
    public double doubleValue() {
        return (double)get();
    }
}
