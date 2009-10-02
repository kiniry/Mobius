package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

final class ConcurrentHashMap$SimpleEntry implements Map$Entry {
    Object key;
    Object value;
    
    public ConcurrentHashMap$SimpleEntry(Object key, Object value) {
        
        this.key = key;
        this.value = value;
    }
    
    public ConcurrentHashMap$SimpleEntry(Map$Entry e) {
        
        this.key = e.getKey();
        this.value = e.getValue();
    }
    
    public Object getKey() {
        return key;
    }
    
    public Object getValue() {
        return value;
    }
    
    public Object setValue(Object value) {
        Object oldValue = this.value;
        this.value = value;
        return oldValue;
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry e = (Map$Entry)(Map$Entry)o;
        return eq(key, e.getKey()) && eq(value, e.getValue());
    }
    
    public int hashCode() {
        return ((key == null) ? 0 : key.hashCode()) ^ ((value == null) ? 0 : value.hashCode());
    }
    
    public String toString() {
        return key + "=" + value;
    }
    
    static boolean eq(Object o1, Object o2) {
        return (o1 == null ? o2 == null : o1.equals(o2));
    }
}
