package java.util;

import java.io.*;

class Hashtable$Entry implements Map$Entry {
    int hash;
    Object key;
    Object value;
    Hashtable$Entry next;
    
    protected Hashtable$Entry(int hash, Object key, Object value, Hashtable$Entry next) {
        
        this.hash = hash;
        this.key = key;
        this.value = value;
        this.next = next;
    }
    
    protected Object clone() {
        return new Hashtable$Entry(hash, key, value, (next == null ? null : (Hashtable$Entry)(Hashtable$Entry)next.clone()));
    }
    
    public Object getKey() {
        return key;
    }
    
    public Object getValue() {
        return value;
    }
    
    public Object setValue(Object value) {
        if (value == null) throw new NullPointerException();
        Object oldValue = this.value;
        this.value = value;
        return oldValue;
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry e = (Map$Entry)(Map$Entry)o;
        return (key == null ? e.getKey() == null : key.equals(e.getKey())) && (value == null ? e.getValue() == null : value.equals(e.getValue()));
    }
    
    public int hashCode() {
        return hash ^ (value == null ? 0 : value.hashCode());
    }
    
    public String toString() {
        return key.toString() + "=" + value.toString();
    }
}
