package java.util;

import java.io.Serializable;
import java.io.ObjectOutputStream;
import java.io.IOException;

class Collections$SynchronizedMap implements Map, Serializable {
    private static final long serialVersionUID = 1978198479659022715L;
    private Map m;
    Object mutex;
    
    Collections$SynchronizedMap(Map m) {
        
        if (m == null) throw new NullPointerException();
        this.m = m;
        mutex = this;
    }
    
    Collections$SynchronizedMap(Map m, Object mutex) {
        
        this.m = m;
        this.mutex = mutex;
    }
    
    public int size() {
        synchronized (mutex) {
            return m.size();
        }
    }
    
    public boolean isEmpty() {
        synchronized (mutex) {
            return m.isEmpty();
        }
    }
    
    public boolean containsKey(Object key) {
        synchronized (mutex) {
            return m.containsKey(key);
        }
    }
    
    public boolean containsValue(Object value) {
        synchronized (mutex) {
            return m.containsValue(value);
        }
    }
    
    public Object get(Object key) {
        synchronized (mutex) {
            return m.get(key);
        }
    }
    
    public Object put(Object key, Object value) {
        synchronized (mutex) {
            return m.put(key, value);
        }
    }
    
    public Object remove(Object key) {
        synchronized (mutex) {
            return m.remove(key);
        }
    }
    
    public void putAll(Map map) {
        synchronized (mutex) {
            m.putAll(map);
        }
    }
    
    public void clear() {
        synchronized (mutex) {
            m.clear();
        }
    }
    private transient Set keySet = null;
    private transient Set entrySet = null;
    private transient Collection values = null;
    
    public Set keySet() {
        synchronized (mutex) {
            if (keySet == null) keySet = new Collections$SynchronizedSet(m.keySet(), mutex);
            return keySet;
        }
    }
    
    public Set entrySet() {
        synchronized (mutex) {
            if (entrySet == null) entrySet = new Collections$SynchronizedSet((Set)m.entrySet(), mutex);
            return entrySet;
        }
    }
    
    public Collection values() {
        synchronized (mutex) {
            if (values == null) values = new Collections$SynchronizedCollection(m.values(), mutex);
            return values;
        }
    }
    
    public boolean equals(Object o) {
        synchronized (mutex) {
            return m.equals(o);
        }
    }
    
    public int hashCode() {
        synchronized (mutex) {
            return m.hashCode();
        }
    }
    
    public String toString() {
        synchronized (mutex) {
            return m.toString();
        }
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        synchronized (mutex) {
            s.defaultWriteObject();
        }
    }
}
