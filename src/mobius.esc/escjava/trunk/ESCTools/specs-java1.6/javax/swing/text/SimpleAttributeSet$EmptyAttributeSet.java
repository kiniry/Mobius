package javax.swing.text;

import java.util.Enumeration;
import java.io.Serializable;

class SimpleAttributeSet$EmptyAttributeSet implements AttributeSet, Serializable {
    
    SimpleAttributeSet$EmptyAttributeSet() {
        
    }
    
    public int getAttributeCount() {
        return 0;
    }
    
    public boolean isDefined(Object attrName) {
        return false;
    }
    
    public boolean isEqual(AttributeSet attr) {
        return (attr.getAttributeCount() == 0);
    }
    
    public AttributeSet copyAttributes() {
        return this;
    }
    
    public Object getAttribute(Object key) {
        return null;
    }
    
    public Enumeration getAttributeNames() {
        return SimpleAttributeSet.access$000();
    }
    
    public boolean containsAttribute(Object name, Object value) {
        return false;
    }
    
    public boolean containsAttributes(AttributeSet attributes) {
        return (attributes.getAttributeCount() == 0);
    }
    
    public AttributeSet getResolveParent() {
        return null;
    }
    
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        return ((obj instanceof AttributeSet) && (((AttributeSet)(AttributeSet)obj).getAttributeCount() == 0));
    }
    
    public int hashCode() {
        return 0;
    }
}
