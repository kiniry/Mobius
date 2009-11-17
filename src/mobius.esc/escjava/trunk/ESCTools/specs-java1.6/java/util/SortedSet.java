package java.util;

public interface SortedSet extends Set {
    
    Comparator comparator();
    
    SortedSet subSet(Object fromElement, Object toElement);
    
    SortedSet headSet(Object toElement);
    
    SortedSet tailSet(Object fromElement);
    
    Object first();
    
    Object last();
}
