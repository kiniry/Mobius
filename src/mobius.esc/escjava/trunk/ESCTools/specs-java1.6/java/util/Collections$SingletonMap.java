package java.util;

import java.io.Serializable;

class Collections$SingletonMap extends AbstractMap implements Serializable {
    private static final long serialVersionUID = -6979724477215052911L;
    private final Object k;
    private final Object v;
    
    Collections$SingletonMap(Object key, Object value) {
        
        k = key;
        v = value;
    }
    
    public int size() {
        return 1;
    }
    
    public boolean isEmpty() {
        return false;
    }
    
    public boolean containsKey(Object key) {
        return Collections.access$000(key, k);
    }
    
    public boolean containsValue(Object value) {
        return Collections.access$000(value, v);
    }
    
    public Object get(Object key) {
        return (Collections.access$000(key, k) ? v : null);
    }
    private transient Set keySet = null;
    private transient Set entrySet = null;
    private transient Collection values = null;
    
    public Set keySet() {
        if (keySet == null) keySet = Collections.singleton(k);
        return keySet;
    }
    
    public Set entrySet() {
        if (entrySet == null) entrySet = Collections.singleton((Map$Entry)new Collections$SingletonMap$ImmutableEntry(k, v));
        return entrySet;
    }
    
    public Collection values() {
        if (values == null) values = Collections.singleton(v);
        return values;
    }
    {
    }
}
