package java.util.concurrent.atomic;

import sun.misc.Unsafe;

public class AtomicBoolean implements java.io.Serializable {
    private static final long serialVersionUID = 4654671469794556979L;
    private static final Unsafe unsafe = Unsafe.getUnsafe();
    private static final long valueOffset;
    static {
        try {
            valueOffset = unsafe.objectFieldOffset(AtomicBoolean.class.getDeclaredField("value"));
        } catch (Exception ex) {
            throw new Error(ex);
        }
    }
    private volatile int value;
    
    public AtomicBoolean(boolean initialValue) {
        
        value = initialValue ? 1 : 0;
    }
    
    public AtomicBoolean() {
        
    }
    
    public final boolean get() {
        return value != 0;
    }
    
    public final boolean compareAndSet(boolean expect, boolean update) {
        int e = expect ? 1 : 0;
        int u = update ? 1 : 0;
        return unsafe.compareAndSwapInt(this, valueOffset, e, u);
    }
    
    public boolean weakCompareAndSet(boolean expect, boolean update) {
        int e = expect ? 1 : 0;
        int u = update ? 1 : 0;
        return unsafe.compareAndSwapInt(this, valueOffset, e, u);
    }
    
    public final void set(boolean newValue) {
        value = newValue ? 1 : 0;
    }
    
    public final boolean getAndSet(boolean newValue) {
        for (; ; ) {
            boolean current = get();
            if (compareAndSet(current, newValue)) return current;
        }
    }
    
    public String toString() {
        return Boolean.toString(get());
    }
}
