package java.util;

import java.io.Serializable;

class Collections$UnmodifiableSortedMap extends Collections$UnmodifiableMap implements SortedMap, Serializable {
    private static final long serialVersionUID = -8806743815996713206L;
    private SortedMap sm;
    
    Collections$UnmodifiableSortedMap(SortedMap m) {
        super(m);
        sm = m;
    }
    
    public Comparator comparator() {
        return sm.comparator();
    }
    
    public SortedMap subMap(Object fromKey, Object toKey) {
        return new Collections$UnmodifiableSortedMap(sm.subMap(fromKey, toKey));
    }
    
    public SortedMap headMap(Object toKey) {
        return new Collections$UnmodifiableSortedMap(sm.headMap(toKey));
    }
    
    public SortedMap tailMap(Object fromKey) {
        return new Collections$UnmodifiableSortedMap(sm.tailMap(fromKey));
    }
    
    public Object firstKey() {
        return sm.firstKey();
    }
    
    public Object lastKey() {
        return sm.lastKey();
    }
}
