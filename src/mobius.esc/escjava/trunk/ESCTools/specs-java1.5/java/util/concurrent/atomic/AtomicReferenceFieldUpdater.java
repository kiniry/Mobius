package java.util.concurrent.atomic;

import java.lang.reflect.*;

public abstract class AtomicReferenceFieldUpdater {
    
    public static AtomicReferenceFieldUpdater newUpdater(Class tclass, Class vclass, String fieldName) {
        return new AtomicReferenceFieldUpdater$AtomicReferenceFieldUpdaterImpl(tclass, vclass, fieldName);
    }
    
    protected AtomicReferenceFieldUpdater() {
        
    }
    
    public abstract boolean compareAndSet(Object obj, Object expect, Object update);
    
    public abstract boolean weakCompareAndSet(Object obj, Object expect, Object update);
    
    public abstract void set(Object obj, Object newValue);
    
    public abstract Object get(Object obj);
    
    public Object getAndSet(Object obj, Object newValue) {
        for (; ; ) {
            Object current = get(obj);
            if (compareAndSet(obj, current, newValue)) return current;
        }
    }
    {
    }
}
