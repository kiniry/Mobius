package java.util.concurrent.atomic;

import java.lang.reflect.*;

public abstract class AtomicLongFieldUpdater {
    
    public static AtomicLongFieldUpdater newUpdater(Class tclass, String fieldName) {
        if (AtomicLong.VM_SUPPORTS_LONG_CAS) return new AtomicLongFieldUpdater$CASUpdater(tclass, fieldName); else return new AtomicLongFieldUpdater$LockedUpdater(tclass, fieldName);
    }
    
    protected AtomicLongFieldUpdater() {
        
    }
    
    public abstract boolean compareAndSet(Object obj, long expect, long update);
    
    public abstract boolean weakCompareAndSet(Object obj, long expect, long update);
    
    public abstract void set(Object obj, long newValue);
    
    public abstract long get(Object obj);
    
    public long getAndSet(Object obj, long newValue) {
        for (; ; ) {
            long current = get(obj);
            if (compareAndSet(obj, current, newValue)) return current;
        }
    }
    
    public long getAndIncrement(Object obj) {
        for (; ; ) {
            long current = get(obj);
            long next = current + 1;
            if (compareAndSet(obj, current, next)) return current;
        }
    }
    
    public long getAndDecrement(Object obj) {
        for (; ; ) {
            long current = get(obj);
            long next = current - 1;
            if (compareAndSet(obj, current, next)) return current;
        }
    }
    
    public long getAndAdd(Object obj, long delta) {
        for (; ; ) {
            long current = get(obj);
            long next = current + delta;
            if (compareAndSet(obj, current, next)) return current;
        }
    }
    
    public long incrementAndGet(Object obj) {
        for (; ; ) {
            long current = get(obj);
            long next = current + 1;
            if (compareAndSet(obj, current, next)) return next;
        }
    }
    
    public long decrementAndGet(Object obj) {
        for (; ; ) {
            long current = get(obj);
            long next = current - 1;
            if (compareAndSet(obj, current, next)) return next;
        }
    }
    
    public long addAndGet(Object obj, long delta) {
        for (; ; ) {
            long current = get(obj);
            long next = current + delta;
            if (compareAndSet(obj, current, next)) return next;
        }
    }
    {
    }
    {
    }
}
