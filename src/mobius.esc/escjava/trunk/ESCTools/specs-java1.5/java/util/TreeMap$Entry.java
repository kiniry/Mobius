package java.util;

class TreeMap$Entry implements Map$Entry {
    Object key;
    Object value;
    TreeMap$Entry left = null;
    TreeMap$Entry right = null;
    TreeMap$Entry parent;
    boolean color = true;
    
    TreeMap$Entry(Object key, Object value, TreeMap$Entry parent) {
        
        this.key = key;
        this.value = value;
        this.parent = parent;
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
        return TreeMap.access$500(key, e.getKey()) && TreeMap.access$500(value, e.getValue());
    }
    
    public int hashCode() {
        int keyHash = (key == null ? 0 : key.hashCode());
        int valueHash = (value == null ? 0 : value.hashCode());
        return keyHash ^ valueHash;
    }
    
    public String toString() {
        return key + "=" + value;
    }
}
