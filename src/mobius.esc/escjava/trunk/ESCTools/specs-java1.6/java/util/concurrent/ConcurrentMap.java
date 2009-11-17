package java.util.concurrent;

import java.util.Map;

public interface ConcurrentMap extends Map {
    
    Object putIfAbsent(Object key, Object value);
    
    boolean remove(Object key, Object value);
    
    boolean replace(Object key, Object oldValue, Object newValue);
    
    Object replace(Object key, Object value);
}
