package java.util;

class Collections$SynchronizedSortedSet extends Collections$SynchronizedSet implements SortedSet {
    private static final long serialVersionUID = 8695801310862127406L;
    private SortedSet ss;
    
    Collections$SynchronizedSortedSet(SortedSet s) {
        super(s);
        ss = s;
    }
    
    Collections$SynchronizedSortedSet(SortedSet s, Object mutex) {
        super(s, mutex);
        ss = s;
    }
    
    public Comparator comparator() {
        synchronized (mutex) {
            return ss.comparator();
        }
    }
    
    public SortedSet subSet(Object fromElement, Object toElement) {
        synchronized (mutex) {
            return new Collections$SynchronizedSortedSet(ss.subSet(fromElement, toElement), mutex);
        }
    }
    
    public SortedSet headSet(Object toElement) {
        synchronized (mutex) {
            return new Collections$SynchronizedSortedSet(ss.headSet(toElement), mutex);
        }
    }
    
    public SortedSet tailSet(Object fromElement) {
        synchronized (mutex) {
            return new Collections$SynchronizedSortedSet(ss.tailSet(fromElement), mutex);
        }
    }
    
    public Object first() {
        synchronized (mutex) {
            return ss.first();
        }
    }
    
    public Object last() {
        synchronized (mutex) {
            return ss.last();
        }
    }
}
