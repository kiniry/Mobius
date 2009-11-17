package javax.swing.text;

import java.util.Enumeration;

public interface AttributeSet {
    
    public int getAttributeCount();
    
    public boolean isDefined(Object attrName);
    
    public boolean isEqual(AttributeSet attr);
    
    public AttributeSet copyAttributes();
    
    public Object getAttribute(Object key);
    
    public Enumeration getAttributeNames();
    
    public boolean containsAttribute(Object name, Object value);
    
    public boolean containsAttributes(AttributeSet attributes);
    
    public AttributeSet getResolveParent();
    public static final Object NameAttribute = StyleConstants.NameAttribute;
    public static final Object ResolveAttribute = StyleConstants.ResolveAttribute;
}
