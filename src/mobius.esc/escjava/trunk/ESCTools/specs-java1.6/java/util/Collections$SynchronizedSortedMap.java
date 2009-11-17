package java.util;

class Collections$SynchronizedSortedMap extends Collections$SynchronizedMap implements SortedMap {
    private static final long serialVersionUID = -8798146769416483793L;
    private SortedMap sm;
    
    Collections$SynchronizedSortedMap(SortedMap m) {
        super(m);
        sm = m;
    }
    
    Collections$SynchronizedSortedMap(SortedMap m, Object mutex) {
        super(m, mutex);
        sm = m;
    }
    
    public Comparator comparator() {
        synchronized (mutex) {
            return sm.comparator();
        }
    }
    
    public SortedMap subMap(Object fromKey, Object toKey) {
        synchronized (mutex) {
            return new Collections$SynchronizedSortedMap(sm.subMap(fromKey, toKey), mutex);
        }
    }
    
    public SortedMap headMap(Object toKey) {
        synchronized (mutex) {
            return new Collections$SynchronizedSortedMap(sm.headMap(toKey), mutex);
        }
    }
    
    public SortedMap tailMap(Object fromKey) {
        synchronized (mutex) {
            return new Collections$SynchronizedSortedMap(sm.tailMap(fromKey), mutex);
        }
    }
    
    public Object firstKey() {
        synchronized (mutex) {
            return sm.firstKey();
        }
    }
    
    public Object lastKey() {
        synchronized (mutex) {
            return sm.lastKey();
        }
    }
}
