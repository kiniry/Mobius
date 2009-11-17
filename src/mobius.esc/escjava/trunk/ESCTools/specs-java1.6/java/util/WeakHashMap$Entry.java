package java.util;

import java.lang.ref.WeakReference;
import java.lang.ref.ReferenceQueue;

class WeakHashMap$Entry extends WeakReference implements Map$Entry {
    
    /*synthetic*/ static Object access$202(WeakHashMap$Entry x0, Object x1) {
        return x0.value = x1;
    }
    
    /*synthetic*/ static Object access$200(WeakHashMap$Entry x0) {
        return x0.value;
    }
    
    /*synthetic*/ static WeakHashMap$Entry access$102(WeakHashMap$Entry x0, WeakHashMap$Entry x1) {
        return x0.next = x1;
    }
    
    /*synthetic*/ static WeakHashMap$Entry access$100(WeakHashMap$Entry x0) {
        return x0.next;
    }
    
    /*synthetic*/ static int access$000(WeakHashMap$Entry x0) {
        return x0.hash;
    }
    private Object value;
    private final int hash;
    private WeakHashMap$Entry next;
    
    WeakHashMap$Entry(Object key, Object value, ReferenceQueue queue, int hash, WeakHashMap$Entry next) {
        super(key, queue);
        this.value = value;
        this.hash = hash;
        this.next = next;
    }
    
    public Object getKey() {
        return WeakHashMap.access$300(get());
    }
    
    public Object getValue() {
        return value;
    }
    
    public Object setValue(Object newValue) {
        Object oldValue = value;
        value = newValue;
        return oldValue;
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry e = (Map$Entry)(Map$Entry)o;
        Object k1 = getKey();
        Object k2 = e.getKey();
        if (k1 == k2 || (k1 != null && k1.equals(k2))) {
            Object v1 = getValue();
            Object v2 = e.getValue();
            if (v1 == v2 || (v1 != null && v1.equals(v2))) return true;
        }
        return false;
    }
    
    public int hashCode() {
        Object k = getKey();
        Object v = getValue();
        return ((k == null ? 0 : k.hashCode()) ^ (v == null ? 0 : v.hashCode()));
    }
    
    public String toString() {
        return getKey() + "=" + getValue();
    }
}
