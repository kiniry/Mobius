package java.lang;

import java.lang.ref.*;

class ThreadLocal$ThreadLocalMap$Entry extends WeakReference {
    
    /*synthetic*/ static Object access$602(ThreadLocal$ThreadLocalMap$Entry x0, Object x1) {
        return x0.value = x1;
    }
    
    /*synthetic*/ static Object access$600(ThreadLocal$ThreadLocalMap$Entry x0) {
        return x0.value;
    }
    
    /*synthetic*/ ThreadLocal$ThreadLocalMap$Entry(ThreadLocal x0, Object x1, java.lang.ThreadLocal$1 x2) {
        this(x0, x1);
    }
    private Object value;
    
    private ThreadLocal$ThreadLocalMap$Entry(ThreadLocal k, Object v) {
        super(k);
        value = v;
    }
}
