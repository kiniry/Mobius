package java.util;

import java.io.*;

class HashMap$Entry implements Map$Entry {
    final Object key;
    Object value;
    final int hash;
    HashMap$Entry next;
    
    HashMap$Entry(int h, Object k, Object v, HashMap$Entry n) {
        
        value = v;
        next = n;
        key = k;
        hash = h;
    }
    
    public Object getKey() {
        return HashMap.unmaskNull(key);
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
        return (key == HashMap.NULL_KEY ? 0 : key.hashCode()) ^ (value == null ? 0 : value.hashCode());
    }
    
    public String toString() {
        return getKey() + "=" + getValue();
    }
    
    void recordAccess(HashMap m) {
    }
    
    void recordRemoval(HashMap m) {
    }
}
