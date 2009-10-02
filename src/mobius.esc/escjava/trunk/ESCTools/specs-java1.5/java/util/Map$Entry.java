package java.util;

public interface Map$Entry {
    
    Object getKey();
    
    Object getValue();
    
    Object setValue(Object value);
    
    boolean equals(Object o);
    
    int hashCode();
}
