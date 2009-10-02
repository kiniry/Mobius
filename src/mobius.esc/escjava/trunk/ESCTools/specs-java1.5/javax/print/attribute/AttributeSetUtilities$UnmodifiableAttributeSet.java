package javax.print.attribute;

import java.io.Serializable;

class AttributeSetUtilities$UnmodifiableAttributeSet implements AttributeSet, Serializable {
    private AttributeSet attrset;
    
    public AttributeSetUtilities$UnmodifiableAttributeSet(AttributeSet attributeSet) {
        
        attrset = attributeSet;
    }
    
    public Attribute get(Class key) {
        return attrset.get(key);
    }
    
    public boolean add(Attribute attribute) {
        throw new UnmodifiableSetException();
    }
    
    public synchronized boolean remove(Class category) {
        throw new UnmodifiableSetException();
    }
    
    public boolean remove(Attribute attribute) {
        throw new UnmodifiableSetException();
    }
    
    public boolean containsKey(Class category) {
        return attrset.containsKey(category);
    }
    
    public boolean containsValue(Attribute attribute) {
        return attrset.containsValue(attribute);
    }
    
    public boolean addAll(AttributeSet attributes) {
        throw new UnmodifiableSetException();
    }
    
    public int size() {
        return attrset.size();
    }
    
    public Attribute[] toArray() {
        return attrset.toArray();
    }
    
    public void clear() {
        throw new UnmodifiableSetException();
    }
    
    public boolean isEmpty() {
        return attrset.isEmpty();
    }
    
    public boolean equals(Object o) {
        return attrset.equals(o);
    }
    
    public int hashCode() {
        return attrset.hashCode();
    }
}
