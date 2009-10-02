package java.util;

import java.io.Serializable;

class Collections$UnmodifiableMap implements Map, Serializable {
    private static final long serialVersionUID = -1034234728574286014L;
    private final Map m;
    
    Collections$UnmodifiableMap(Map m) {
        
        if (m == null) throw new NullPointerException();
        this.m = m;
    }
    
    public int size() {
        return m.size();
    }
    
    public boolean isEmpty() {
        return m.isEmpty();
    }
    
    public boolean containsKey(Object key) {
        return m.containsKey(key);
    }
    
    public boolean containsValue(Object val) {
        return m.containsValue(val);
    }
    
    public Object get(Object key) {
        return m.get(key);
    }
    
    public Object put(Object key, Object value) {
        throw new UnsupportedOperationException();
    }
    
    public Object remove(Object key) {
        throw new UnsupportedOperationException();
    }
    
    public void putAll(Map t) {
        throw new UnsupportedOperationException();
    }
    
    public void clear() {
        throw new UnsupportedOperationException();
    }
    private transient Set keySet = null;
    private transient Set entrySet = null;
    private transient Collection values = null;
    
    public Set keySet() {
        if (keySet == null) keySet = Collections.unmodifiableSet(m.keySet());
        return keySet;
    }
    
    public Set entrySet() {
        if (entrySet == null) entrySet = new Collections$UnmodifiableMap$UnmodifiableEntrySet(m.entrySet());
        return entrySet;
    }
    
    public Collection values() {
        if (values == null) values = Collections.unmodifiableCollection(m.values());
        return values;
    }
    
    public boolean equals(Object o) {
        return m.equals(o);
    }
    
    public int hashCode() {
        return m.hashCode();
    }
    
    public String toString() {
        return m.toString();
    }
    {
    }
}
