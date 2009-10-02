package java.lang;

import java.lang.ref.*;

public class ThreadLocal {
    
    /*synthetic*/ static int access$400(ThreadLocal x0) {
        return x0.threadLocalHashCode;
    }
    {
    }
    private final int threadLocalHashCode = nextHashCode();
    private static int nextHashCode = 0;
    private static final int HASH_INCREMENT = 1640531527;
    
    private static synchronized int nextHashCode() {
        int h = nextHashCode;
        nextHashCode = h + HASH_INCREMENT;
        return h;
    }
    
    protected Object initialValue() {
        return null;
    }
    
    public ThreadLocal() {
        
    }
    
    public Object get() {
        Thread t = Thread.currentThread();
        ThreadLocal$ThreadLocalMap map = getMap(t);
        if (map != null) return (Object)ThreadLocal.ThreadLocalMap.access$000(map, this);
        Object value = initialValue();
        createMap(t, value);
        return value;
    }
    
    public void set(Object value) {
        Thread t = Thread.currentThread();
        ThreadLocal$ThreadLocalMap map = getMap(t);
        if (map != null) ThreadLocal.ThreadLocalMap.access$100(map, this, value); else createMap(t, value);
    }
    
    public void remove() {
        ThreadLocal$ThreadLocalMap m = getMap(Thread.currentThread());
        if (m != null) ThreadLocal.ThreadLocalMap.access$200(m, this);
    }
    
    ThreadLocal$ThreadLocalMap getMap(Thread t) {
        return t.threadLocals;
    }
    
    void createMap(Thread t, Object firstValue) {
        t.threadLocals = new ThreadLocal$ThreadLocalMap(this, firstValue);
    }
    
    static ThreadLocal$ThreadLocalMap createInheritedMap(ThreadLocal$ThreadLocalMap parentMap) {
        return new ThreadLocal$ThreadLocalMap(parentMap, null);
    }
    
    Object childValue(Object parentValue) {
        throw new UnsupportedOperationException();
    }
    {
    }
}
