package java.util.concurrent.atomic;

import sun.misc.Unsafe;
import java.util.*;

public class AtomicLongArray implements java.io.Serializable {
    private static final long serialVersionUID = -2308431214976778248L;
    private static final Unsafe unsafe = Unsafe.getUnsafe();
    private static final int base = unsafe.arrayBaseOffset(long[].class);
    private static final int scale = unsafe.arrayIndexScale(long[].class);
    private final long[] array;
    
    private long rawIndex(int i) {
        if (i < 0 || i >= array.length) throw new IndexOutOfBoundsException("index " + i);
        return base + i * scale;
    }
    
    public AtomicLongArray(int length) {
        
        array = new long[length];
        if (length > 0) unsafe.putLongVolatile(array, rawIndex(0), 0);
    }
    
    public AtomicLongArray(long[] array) {
        
        if (array == null) throw new NullPointerException();
        int length = array.length;
        this.array = new long[length];
        if (length > 0) {
            int last = length - 1;
            for (int i = 0; i < last; ++i) this.array[i] = array[i];
            unsafe.putLongVolatile(this.array, rawIndex(last), array[last]);
        }
    }
    
    public final int length() {
        return array.length;
    }
    
    public final long get(int i) {
        return unsafe.getLongVolatile(array, rawIndex(i));
    }
    
    public final void set(int i, long newValue) {
        unsafe.putLongVolatile(array, rawIndex(i), newValue);
    }
    
    public final long getAndSet(int i, long newValue) {
        while (true) {
            long current = get(i);
            if (compareAndSet(i, current, newValue)) return current;
        }
    }
    
    public final boolean compareAndSet(int i, long expect, long update) {
        return unsafe.compareAndSwapLong(array, rawIndex(i), expect, update);
    }
    
    public final boolean weakCompareAndSet(int i, long expect, long update) {
        return compareAndSet(i, expect, update);
    }
    
    public final long getAndIncrement(int i) {
        while (true) {
            long current = get(i);
            long next = current + 1;
            if (compareAndSet(i, current, next)) return current;
        }
    }
    
    public final long getAndDecrement(int i) {
        while (true) {
            long current = get(i);
            long next = current - 1;
            if (compareAndSet(i, current, next)) return current;
        }
    }
    
    public final long getAndAdd(int i, long delta) {
        while (true) {
            long current = get(i);
            long next = current + delta;
            if (compareAndSet(i, current, next)) return current;
        }
    }
    
    public final long incrementAndGet(int i) {
        while (true) {
            long current = get(i);
            long next = current + 1;
            if (compareAndSet(i, current, next)) return next;
        }
    }
    
    public final long decrementAndGet(int i) {
        while (true) {
            long current = get(i);
            long next = current - 1;
            if (compareAndSet(i, current, next)) return next;
        }
    }
    
    public long addAndGet(int i, long delta) {
        while (true) {
            long current = get(i);
            long next = current + delta;
            if (compareAndSet(i, current, next)) return next;
        }
    }
    
    public String toString() {
        if (array.length > 0) get(0);
        return Arrays.toString(array);
    }
}
