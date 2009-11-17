package java.util;

import java.io.Serializable;
import java.lang.reflect.Array;

class Collections$CheckedMap implements Map, Serializable {
    private static final long serialVersionUID = 5742860141034234728L;
    private final Map m;
    final Class keyType;
    final Class valueType;
    
    private void typeCheck(Object key, Object value) {
        if (!keyType.isInstance(key)) throw new ClassCastException("Attempt to insert " + key.getClass() + " key into collection with key type " + keyType);
        if (!valueType.isInstance(value)) throw new ClassCastException("Attempt to insert " + value.getClass() + " value into collection with value type " + valueType);
    }
    
    Collections$CheckedMap(Map m, Class keyType, Class valueType) {
        
        if (m == null || keyType == null || valueType == null) throw new NullPointerException();
        this.m = m;
        this.keyType = keyType;
        this.valueType = valueType;
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
    
    public boolean containsValue(Object v) {
        return m.containsValue(v);
    }
    
    public Object get(Object key) {
        return m.get(key);
    }
    
    public Object remove(Object key) {
        return m.remove(key);
    }
    
    public void clear() {
        m.clear();
    }
    
    public Set keySet() {
        return m.keySet();
    }
    
    public Collection values() {
        return m.values();
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
    
    public Object put(Object key, Object value) {
        typeCheck(key, value);
        return m.put(key, value);
    }
    
    public void putAll(Map t) {
        Object[] keys = null;
        try {
            keys = t.keySet().toArray(zeroLengthKeyArray());
        } catch (ArrayStoreException e) {
            throw new ClassCastException();
        }
        Object[] values = null;
        try {
            values = t.values().toArray(zeroLengthValueArray());
        } catch (ArrayStoreException e) {
            throw new ClassCastException();
        }
        if (keys.length != values.length) throw new ConcurrentModificationException();
        for (int i = 0; i < keys.length; i++) m.put(keys[i], values[i]);
    }
    private Object[] zeroLengthKeyArray = null;
    private Object[] zeroLengthValueArray = null;
    
    private Object[] zeroLengthKeyArray() {
        if (zeroLengthKeyArray == null) zeroLengthKeyArray = (Object[])(Object[])Array.newInstance(keyType, 0);
        return zeroLengthKeyArray;
    }
    
    private Object[] zeroLengthValueArray() {
        if (zeroLengthValueArray == null) zeroLengthValueArray = (Object[])(Object[])Array.newInstance(valueType, 0);
        return zeroLengthValueArray;
    }
    private transient Set entrySet = null;
    
    public Set entrySet() {
        if (entrySet == null) entrySet = new Collections$CheckedMap$CheckedEntrySet(m.entrySet(), valueType);
        return entrySet;
    }
    {
    }
}
