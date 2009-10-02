package javax.print.attribute;

public interface AttributeSet {
    
    public Attribute get(Class category);
    
    public boolean add(Attribute attribute);
    
    public boolean remove(Class category);
    
    public boolean remove(Attribute attribute);
    
    public boolean containsKey(Class category);
    
    public boolean containsValue(Attribute attribute);
    
    public boolean addAll(AttributeSet attributes);
    
    public int size();
    
    public Attribute[] toArray();
    
    public void clear();
    
    public boolean isEmpty();
    
    public boolean equals(Object object);
    
    public int hashCode();
}
