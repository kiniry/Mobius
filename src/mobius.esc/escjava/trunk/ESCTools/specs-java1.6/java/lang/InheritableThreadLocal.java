package java.lang;

import java.lang.ref.*;

public class InheritableThreadLocal extends ThreadLocal {
    
    public InheritableThreadLocal() {
        
    }
    
    protected Object childValue(Object parentValue) {
        return parentValue;
    }
    
    ThreadLocal$ThreadLocalMap getMap(Thread t) {
        return t.inheritableThreadLocals;
    }
    
    void createMap(Thread t, Object firstValue) {
        t.inheritableThreadLocals = new ThreadLocal$ThreadLocalMap(this, firstValue);
    }
}
