package java.util;

import java.io.Serializable;

class Collections$CheckedSortedSet extends Collections$CheckedSet implements SortedSet, Serializable {
    private static final long serialVersionUID = 1599911165492914959L;
    private final SortedSet ss;
    
    Collections$CheckedSortedSet(SortedSet s, Class type) {
        super(s, type);
        ss = s;
    }
    
    public Comparator comparator() {
        return ss.comparator();
    }
    
    public Object first() {
        return ss.first();
    }
    
    public Object last() {
        return ss.last();
    }
    
    public SortedSet subSet(Object fromElement, Object toElement) {
        return new Collections$CheckedSortedSet(ss.subSet(fromElement, toElement), type);
    }
    
    public SortedSet headSet(Object toElement) {
        return new Collections$CheckedSortedSet(ss.headSet(toElement), type);
    }
    
    public SortedSet tailSet(Object fromElement) {
        return new Collections$CheckedSortedSet(ss.tailSet(fromElement), type);
    }
}
