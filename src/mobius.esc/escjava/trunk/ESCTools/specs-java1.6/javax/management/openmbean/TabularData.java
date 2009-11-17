package javax.management.openmbean;

import java.util.Set;
import java.util.Collection;

public interface TabularData {
    
    public TabularType getTabularType();
    
    public Object[] calculateIndex(CompositeData value);
    
    public int size();
    
    public boolean isEmpty();
    
    public boolean containsKey(Object[] key);
    
    public boolean containsValue(CompositeData value);
    
    public CompositeData get(Object[] key);
    
    public void put(CompositeData value);
    
    public CompositeData remove(Object[] key);
    
    public void putAll(CompositeData[] values);
    
    public void clear();
    
    public Set keySet();
    
    public Collection values();
    
    public boolean equals(Object obj);
    
    public int hashCode();
    
    public String toString();
}
