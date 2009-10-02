package java.util;

import java.io.Serializable;

class Collections$EmptyMap extends AbstractMap implements Serializable {
    
    /*synthetic*/ Collections$EmptyMap(java.util.Collections$1 x0) {
        this();
    }
    
    private Collections$EmptyMap() {
        
    }
    private static final long serialVersionUID = 6428348081105594320L;
    
    public int size() {
        return 0;
    }
    
    public boolean isEmpty() {
        return true;
    }
    
    public boolean containsKey(Object key) {
        return false;
    }
    
    public boolean containsValue(Object value) {
        return false;
    }
    
    public Object get(Object key) {
        return null;
    }
    
    public Set keySet() {
        return Collections.emptySet();
    }
    
    public Collection values() {
        return Collections.emptySet();
    }
    
    public Set entrySet() {
        return Collections.emptySet();
    }
    
    public boolean equals(Object o) {
        return (o instanceof Map) && ((Map)(Map)o).size() == 0;
    }
    
    public int hashCode() {
        return 0;
    }
    
    private Object readResolve() {
        return Collections.EMPTY_MAP;
    }
}
