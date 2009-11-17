package java.util;

public interface SortedMap extends Map {
    
    Comparator comparator();
    
    SortedMap subMap(Object fromKey, Object toKey);
    
    SortedMap headMap(Object toKey);
    
    SortedMap tailMap(Object fromKey);
    
    Object firstKey();
    
    Object lastKey();
}
