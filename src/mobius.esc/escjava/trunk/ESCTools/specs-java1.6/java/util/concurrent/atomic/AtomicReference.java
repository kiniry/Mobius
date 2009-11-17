package java.util.concurrent.atomic;

import sun.misc.Unsafe;

public class AtomicReference implements java.io.Serializable {
    private static final long serialVersionUID = -1848883965231344442L;
    private static final Unsafe unsafe = Unsafe.getUnsafe();
    private static final long valueOffset;
    static {
        try {
            valueOffset = unsafe.objectFieldOffset(AtomicReference.class.getDeclaredField("value"));
        } catch (Exception ex) {
            throw new Error(ex);
        }
    }
    private volatile Object value;
    
    public AtomicReference(Object initialValue) {
        
        value = initialValue;
    }
    
    public AtomicReference() {
        
    }
    
    public final Object get() {
        return value;
    }
    
    public final void set(Object newValue) {
        value = newValue;
    }
    
    public final boolean compareAndSet(Object expect, Object update) {
        return unsafe.compareAndSwapObject(this, valueOffset, expect, update);
    }
    
    public final boolean weakCompareAndSet(Object expect, Object update) {
        return unsafe.compareAndSwapObject(this, valueOffset, expect, update);
    }
    
    public final Object getAndSet(Object newValue) {
        while (true) {
            Object x = get();
            if (compareAndSet(x, newValue)) return x;
        }
    }
    
    public String toString() {
        return String.valueOf(get());
    }
}
