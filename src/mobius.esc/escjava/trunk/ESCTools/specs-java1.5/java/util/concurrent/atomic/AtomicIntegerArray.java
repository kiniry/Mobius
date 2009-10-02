package java.util.concurrent.atomic;

import sun.misc.Unsafe;
import java.util.*;

public class AtomicIntegerArray implements java.io.Serializable {
    private static final long serialVersionUID = 2862133569453604235L;
    private static final Unsafe unsafe = Unsafe.getUnsafe();
    private static final int base = unsafe.arrayBaseOffset(int[].class);
    private static final int scale = unsafe.arrayIndexScale(int[].class);
    private final int[] array;
    
    private long rawIndex(int i) {
        if (i < 0 || i >= array.length) throw new IndexOutOfBoundsException("index " + i);
        return base + i * scale;
    }
    
    public AtomicIntegerArray(int length) {
        
        array = new int[length];
        if (length > 0) unsafe.putIntVolatile(array, rawIndex(0), 0);
    }
    
    public AtomicIntegerArray(int[] array) {
        
        if (array == null) throw new NullPointerException();
        int length = array.length;
        this.array = new int[length];
        if (length > 0) {
            int last = length - 1;
            for (int i = 0; i < last; ++i) this.array[i] = array[i];
            unsafe.putIntVolatile(this.array, rawIndex(last), array[last]);
        }
    }
    
    public final int length() {
        return array.length;
    }
    
    public final int get(int i) {
        return unsafe.getIntVolatile(array, rawIndex(i));
    }
    
    public final void set(int i, int newValue) {
        unsafe.putIntVolatile(array, rawIndex(i), newValue);
    }
    
    public final int getAndSet(int i, int newValue) {
        while (true) {
            int current = get(i);
            if (compareAndSet(i, current, newValue)) return current;
        }
    }
    
    public final boolean compareAndSet(int i, int expect, int update) {
        return unsafe.compareAndSwapInt(array, rawIndex(i), expect, update);
    }
    
    public final boolean weakCompareAndSet(int i, int expect, int update) {
        return compareAndSet(i, expect, update);
    }
    
    public final int getAndIncrement(int i) {
        while (true) {
            int current = get(i);
            int next = current + 1;
            if (compareAndSet(i, current, next)) return current;
        }
    }
    
    public final int getAndDecrement(int i) {
        while (true) {
            int current = get(i);
            int next = current - 1;
            if (compareAndSet(i, current, next)) return current;
        }
    }
    
    public final int getAndAdd(int i, int delta) {
        while (true) {
            int current = get(i);
            int next = current + delta;
            if (compareAndSet(i, current, next)) return current;
        }
    }
    
    public final int incrementAndGet(int i) {
        while (true) {
            int current = get(i);
            int next = current + 1;
            if (compareAndSet(i, current, next)) return next;
        }
    }
    
    public final int decrementAndGet(int i) {
        while (true) {
            int current = get(i);
            int next = current - 1;
            if (compareAndSet(i, current, next)) return next;
        }
    }
    
    public final int addAndGet(int i, int delta) {
        while (true) {
            int current = get(i);
            int next = current + delta;
            if (compareAndSet(i, current, next)) return next;
        }
    }
    
    public String toString() {
        if (array.length > 0) get(0);
        return Arrays.toString(array);
    }
}
