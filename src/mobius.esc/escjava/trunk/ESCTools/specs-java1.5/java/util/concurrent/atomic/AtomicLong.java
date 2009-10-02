package java.util.concurrent.atomic;

import sun.misc.Unsafe;

public class AtomicLong extends Number implements java.io.Serializable {
    private static final long serialVersionUID = 1927816293512124184L;
    private static final Unsafe unsafe = Unsafe.getUnsafe();
    private static final long valueOffset;
    static final boolean VM_SUPPORTS_LONG_CAS = VMSupportsCS8();
    
    private static native boolean VMSupportsCS8();
    static {
        try {
            valueOffset = unsafe.objectFieldOffset(AtomicLong.class.getDeclaredField("value"));
        } catch (Exception ex) {
            throw new Error(ex);
        }
    }
    private volatile long value;
    
    public AtomicLong(long initialValue) {
        
        value = initialValue;
    }
    
    public AtomicLong() {
        
    }
    
    public final long get() {
        return value;
    }
    
    public final void set(long newValue) {
        value = newValue;
    }
    
    public final long getAndSet(long newValue) {
        while (true) {
            long current = get();
            if (compareAndSet(current, newValue)) return current;
        }
    }
    
    public final boolean compareAndSet(long expect, long update) {
        return unsafe.compareAndSwapLong(this, valueOffset, expect, update);
    }
    
    public final boolean weakCompareAndSet(long expect, long update) {
        return unsafe.compareAndSwapLong(this, valueOffset, expect, update);
    }
    
    public final long getAndIncrement() {
        while (true) {
            long current = get();
            long next = current + 1;
            if (compareAndSet(current, next)) return current;
        }
    }
    
    public final long getAndDecrement() {
        while (true) {
            long current = get();
            long next = current - 1;
            if (compareAndSet(current, next)) return current;
        }
    }
    
    public final long getAndAdd(long delta) {
        while (true) {
            long current = get();
            long next = current + delta;
            if (compareAndSet(current, next)) return current;
        }
    }
    
    public final long incrementAndGet() {
        for (; ; ) {
            long current = get();
            long next = current + 1;
            if (compareAndSet(current, next)) return next;
        }
    }
    
    public final long decrementAndGet() {
        for (; ; ) {
            long current = get();
            long next = current - 1;
            if (compareAndSet(current, next)) return next;
        }
    }
    
    public final long addAndGet(long delta) {
        for (; ; ) {
            long current = get();
            long next = current + delta;
            if (compareAndSet(current, next)) return next;
        }
    }
    
    public String toString() {
        return Long.toString(get());
    }
    
    public int intValue() {
        return (int)get();
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
