package javax.print.attribute;

import java.io.Serializable;

class AttributeSetUtilities$SynchronizedAttributeSet implements AttributeSet, Serializable {
    private AttributeSet attrset;
    
    public AttributeSetUtilities$SynchronizedAttributeSet(AttributeSet attributeSet) {
        
        attrset = attributeSet;
    }
    
    public synchronized Attribute get(Class category) {
        return attrset.get(category);
    }
    
    public synchronized boolean add(Attribute attribute) {
        return attrset.add(attribute);
    }
    
    public synchronized boolean remove(Class category) {
        return attrset.remove(category);
    }
    
    public synchronized boolean remove(Attribute attribute) {
        return attrset.remove(attribute);
    }
    
    public synchronized boolean containsKey(Class category) {
        return attrset.containsKey(category);
    }
    
    public synchronized boolean containsValue(Attribute attribute) {
        return attrset.containsValue(attribute);
    }
    
    public synchronized boolean addAll(AttributeSet attributes) {
        return attrset.addAll(attributes);
    }
    
    public synchronized int size() {
        return attrset.size();
    }
    
    public synchronized Attribute[] toArray() {
        return attrset.toArray();
    }
    
    public synchronized void clear() {
        attrset.clear();
    }
    
    public synchronized boolean isEmpty() {
        return attrset.isEmpty();
    }
    
    public synchronized boolean equals(Object o) {
        return attrset.equals(o);
    }
    
    public synchronized int hashCode() {
        return attrset.hashCode();
    }
}
