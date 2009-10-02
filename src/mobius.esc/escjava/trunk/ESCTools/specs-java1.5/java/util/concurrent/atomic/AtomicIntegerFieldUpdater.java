package java.util.concurrent.atomic;

import java.lang.reflect.*;

public abstract class AtomicIntegerFieldUpdater {
    
    public static AtomicIntegerFieldUpdater newUpdater(Class tclass, String fieldName) {
        return new AtomicIntegerFieldUpdater$AtomicIntegerFieldUpdaterImpl(tclass, fieldName);
    }
    
    protected AtomicIntegerFieldUpdater() {
        
    }
    
    public abstract boolean compareAndSet(Object obj, int expect, int update);
    
    public abstract boolean weakCompareAndSet(Object obj, int expect, int update);
    
    public abstract void set(Object obj, int newValue);
    
    public abstract int get(Object obj);
    
    public int getAndSet(Object obj, int newValue) {
        for (; ; ) {
            int current = get(obj);
            if (compareAndSet(obj, current, newValue)) return current;
        }
    }
    
    public int getAndIncrement(Object obj) {
        for (; ; ) {
            int current = get(obj);
            int next = current + 1;
            if (compareAndSet(obj, current, next)) return current;
        }
    }
    
    public int getAndDecrement(Object obj) {
        for (; ; ) {
            int current = get(obj);
            int next = current - 1;
            if (compareAndSet(obj, current, next)) return current;
        }
    }
    
    public int getAndAdd(Object obj, int delta) {
        for (; ; ) {
            int current = get(obj);
            int next = current + delta;
            if (compareAndSet(obj, current, next)) return current;
        }
    }
    
    public int incrementAndGet(Object obj) {
        for (; ; ) {
            int current = get(obj);
            int next = current + 1;
            if (compareAndSet(obj, current, next)) return next;
        }
    }
    
    public int decrementAndGet(Object obj) {
        for (; ; ) {
            int current = get(obj);
            int next = current - 1;
            if (compareAndSet(obj, current, next)) return next;
        }
    }
    
    public int addAndGet(Object obj, int delta) {
        for (; ; ) {
            int current = get(obj);
            int next = current + delta;
            if (compareAndSet(obj, current, next)) return next;
        }
    }
    {
    }
}
