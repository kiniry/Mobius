package java.util;

class Collections$CheckedMap$CheckedEntrySet$CheckedEntry implements Map$Entry {
    private Map$Entry e;
    private Class valueType;
    
    Collections$CheckedMap$CheckedEntrySet$CheckedEntry(Map$Entry e, Class valueType) {
        
        this.e = e;
        this.valueType = valueType;
    }
    
    public Object getKey() {
        return e.getKey();
    }
    
    public Object getValue() {
        return e.getValue();
    }
    
    public int hashCode() {
        return e.hashCode();
    }
    
    public String toString() {
        return e.toString();
    }
    
    public Object setValue(Object value) {
        if (!valueType.isInstance(value)) throw new ClassCastException("Attempt to insert " + value.getClass() + " value into collection with value type " + valueType);
        return e.setValue(value);
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry t = (Map$Entry)(Map$Entry)o;
        return Collections.access$000(e.getKey(), t.getKey()) && Collections.access$000(e.getValue(), t.getValue());
    }
}
