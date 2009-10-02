package java.util;

import java.io.Serializable;

class Collections$UnmodifiableSortedSet extends Collections$UnmodifiableSet implements SortedSet, Serializable {
    private static final long serialVersionUID = -4929149591599911165L;
    private SortedSet ss;
    
    Collections$UnmodifiableSortedSet(SortedSet s) {
        super(s);
        ss = s;
    }
    
    public Comparator comparator() {
        return ss.comparator();
    }
    
    public SortedSet subSet(Object fromElement, Object toElement) {
        return new Collections$UnmodifiableSortedSet(ss.subSet(fromElement, toElement));
    }
    
    public SortedSet headSet(Object toElement) {
        return new Collections$UnmodifiableSortedSet(ss.headSet(toElement));
    }
    
    public SortedSet tailSet(Object fromElement) {
        return new Collections$UnmodifiableSortedSet(ss.tailSet(fromElement));
    }
    
    public Object first() {
        return ss.first();
    }
    
    public Object last() {
        return ss.last();
    }
}
