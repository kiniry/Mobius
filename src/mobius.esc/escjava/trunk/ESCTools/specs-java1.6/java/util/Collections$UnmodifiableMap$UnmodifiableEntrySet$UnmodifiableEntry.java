package java.util;

class Collections$UnmodifiableMap$UnmodifiableEntrySet$UnmodifiableEntry implements Map$Entry {
    private Map$Entry e;
    
    Collections$UnmodifiableMap$UnmodifiableEntrySet$UnmodifiableEntry(Map$Entry e) {
        
        this.e = e;
    }
    
    public Object getKey() {
        return e.getKey();
    }
    
    public Object getValue() {
        return e.getValue();
    }
    
    public Object setValue(Object value) {
        throw new UnsupportedOperationException();
    }
    
    public int hashCode() {
        return e.hashCode();
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry t = (Map$Entry)(Map$Entry)o;
        return Collections.access$000(e.getKey(), t.getKey()) && Collections.access$000(e.getValue(), t.getValue());
    }
    
    public String toString() {
        return e.toString();
    }
}
