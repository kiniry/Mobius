package java.util;

class Collections$SingletonMap$ImmutableEntry implements Map$Entry {
    final Object k;
    final Object v;
    
    Collections$SingletonMap$ImmutableEntry(Object key, Object value) {
        
        k = key;
        v = value;
    }
    
    public Object getKey() {
        return k;
    }
    
    public Object getValue() {
        return v;
    }
    
    public Object setValue(Object value) {
        throw new UnsupportedOperationException();
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry e = (Map$Entry)(Map$Entry)o;
        return Collections.access$000(e.getKey(), k) && Collections.access$000(e.getValue(), v);
    }
    
    public int hashCode() {
        return ((k == null ? 0 : k.hashCode()) ^ (v == null ? 0 : v.hashCode()));
    }
    
    public String toString() {
        return k + "=" + v;
    }
}
