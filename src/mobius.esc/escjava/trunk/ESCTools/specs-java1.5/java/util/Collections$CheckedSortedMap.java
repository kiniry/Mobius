package java.util;

import java.io.Serializable;

class Collections$CheckedSortedMap extends Collections$CheckedMap implements SortedMap, Serializable {
    private static final long serialVersionUID = 1599671320688067438L;
    private SortedMap sm;
    
    Collections$CheckedSortedMap(SortedMap m, Class keyType, Class valueType) {
        super(m, keyType, valueType);
        sm = m;
    }
    
    public Comparator comparator() {
        return sm.comparator();
    }
    
    public Object firstKey() {
        return sm.firstKey();
    }
    
    public Object lastKey() {
        return sm.lastKey();
    }
    
    public SortedMap subMap(Object fromKey, Object toKey) {
        return new Collections$CheckedSortedMap(sm.subMap(fromKey, toKey), keyType, valueType);
    }
    
    public SortedMap headMap(Object toKey) {
        return new Collections$CheckedSortedMap(sm.headMap(toKey), keyType, valueType);
    }
    
    public SortedMap tailMap(Object fromKey) {
        return new Collections$CheckedSortedMap(sm.tailMap(fromKey), keyType, valueType);
    }
}
