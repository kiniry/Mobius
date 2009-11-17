package javax.swing.text;

import java.util.Enumeration;

public interface MutableAttributeSet extends AttributeSet {
    
    public void addAttribute(Object name, Object value);
    
    public void addAttributes(AttributeSet attributes);
    
    public void removeAttribute(Object name);
    
    public void removeAttributes(Enumeration names);
    
    public void removeAttributes(AttributeSet attributes);
    
    public void setResolveParent(AttributeSet parent);
}
