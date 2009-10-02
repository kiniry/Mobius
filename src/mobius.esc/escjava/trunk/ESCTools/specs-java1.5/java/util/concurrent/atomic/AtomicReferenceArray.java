package java.util.concurrent.atomic;

import sun.misc.Unsafe;
import java.util.*;

public class AtomicReferenceArray implements java.io.Serializable {
    private static final long serialVersionUID = -6209656149925076980L;
    private static final Unsafe unsafe = Unsafe.getUnsafe();
    private static final int base = unsafe.arrayBaseOffset(Object[].class);
    private static final int scale = unsafe.arrayIndexScale(Object[].class);
    private final Object[] array;
    
    private long rawIndex(int i) {
        if (i < 0 || i >= array.length) throw new IndexOutOfBoundsException("index " + i);
        return base + i * scale;
    }
    
    public AtomicReferenceArray(int length) {
        
        array = new Object[length];
        if (length > 0) unsafe.putObjectVolatile(array, rawIndex(0), null);
    }
    
    public AtomicReferenceArray(Object[] array) {
        
        if (array == null) throw new NullPointerException();
        int length = array.length;
        this.array = new Object[length];
        if (length > 0) {
            int last = length - 1;
            for (int i = 0; i < last; ++i) this.array[i] = array[i];
            Object e = array[last];
            unsafe.putObjectVolatile(this.array, rawIndex(last), e);
        }
    }
    
    public final int length() {
        return array.length;
    }
    
    public final Object get(int i) {
        return (Object)unsafe.getObjectVolatile(array, rawIndex(i));
    }
    
    public final void set(int i, Object newValue) {
        unsafe.putObjectVolatile(array, rawIndex(i), newValue);
    }
    
    public final Object getAndSet(int i, Object newValue) {
        while (true) {
            Object current = get(i);
            if (compareAndSet(i, current, newValue)) return current;
        }
    }
    
    public final boolean compareAndSet(int i, Object expect, Object update) {
        return unsafe.compareAndSwapObject(array, rawIndex(i), expect, update);
    }
    
    public final boolean weakCompareAndSet(int i, Object expect, Object update) {
        return compareAndSet(i, expect, update);
    }
    
    public String toString() {
        if (array.length > 0) get(0);
        return Arrays.toString(array);
    }
}
