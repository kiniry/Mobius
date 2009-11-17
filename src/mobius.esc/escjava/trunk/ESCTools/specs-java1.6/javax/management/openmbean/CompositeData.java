package javax.management.openmbean;

import java.util.Collection;

public interface CompositeData {
    
    public CompositeType getCompositeType();
    
    public Object get(String key);
    
    public Object[] getAll(String[] keys);
    
    public boolean containsKey(String key);
    
    public boolean containsValue(Object value);
    
    public Collection values();
    
    public boolean equals(Object obj);
    
    public int hashCode();
    
    public String toString();
}
