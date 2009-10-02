package javax.swing.text.html;

import javax.swing.text.*;
import java.io.Serializable;
import java.util.*;

class MuxingAttributeSet implements AttributeSet, Serializable {
    
    public MuxingAttributeSet(AttributeSet[] attrs) {
        
        this.attrs = attrs;
    }
    
    protected MuxingAttributeSet() {
        
    }
    
    protected synchronized void setAttributes(AttributeSet[] attrs) {
        this.attrs = attrs;
    }
    
    protected synchronized AttributeSet[] getAttributes() {
        return attrs;
    }
    
    protected synchronized void insertAttributeSetAt(AttributeSet as, int index) {
        int numAttrs = attrs.length;
        AttributeSet[] newAttrs = new AttributeSet[numAttrs + 1];
        if (index < numAttrs) {
            if (index > 0) {
                System.arraycopy(attrs, 0, newAttrs, 0, index);
                System.arraycopy(attrs, index, newAttrs, index + 1, numAttrs - index);
            } else {
                System.arraycopy(attrs, 0, newAttrs, 1, numAttrs);
            }
        } else {
            System.arraycopy(attrs, 0, newAttrs, 0, numAttrs);
        }
        newAttrs[index] = as;
        attrs = newAttrs;
    }
    
    protected synchronized void removeAttributeSetAt(int index) {
        int numAttrs = attrs.length;
        AttributeSet[] newAttrs = new AttributeSet[numAttrs - 1];
        if (numAttrs > 0) {
            if (index == 0) {
                System.arraycopy(attrs, 1, newAttrs, 0, numAttrs - 1);
            } else if (index < (numAttrs - 1)) {
                System.arraycopy(attrs, 0, newAttrs, 0, index);
                System.arraycopy(attrs, index + 1, newAttrs, index, numAttrs - index - 1);
            } else {
                System.arraycopy(attrs, 0, newAttrs, 0, numAttrs - 1);
            }
        }
        attrs = newAttrs;
    }
    
    public int getAttributeCount() {
        AttributeSet[] as = getAttributes();
        int n = 0;
        for (int i = 0; i < as.length; i++) {
            n += as[i].getAttributeCount();
        }
        return n;
    }
    
    public boolean isDefined(Object key) {
        AttributeSet[] as = getAttributes();
        for (int i = 0; i < as.length; i++) {
            if (as[i].isDefined(key)) {
                return true;
            }
        }
        return false;
    }
    
    public boolean isEqual(AttributeSet attr) {
        return ((getAttributeCount() == attr.getAttributeCount()) && containsAttributes(attr));
    }
    
    public AttributeSet copyAttributes() {
        AttributeSet[] as = getAttributes();
        MutableAttributeSet a = new SimpleAttributeSet();
        int n = 0;
        for (int i = as.length - 1; i >= 0; i--) {
            a.addAttributes(as[i]);
        }
        return a;
    }
    
    public Object getAttribute(Object key) {
        AttributeSet[] as = getAttributes();
        int n = as.length;
        for (int i = 0; i < n; i++) {
            Object o = as[i].getAttribute(key);
            if (o != null) {
                return o;
            }
        }
        return null;
    }
    
    public Enumeration getAttributeNames() {
        return new MuxingAttributeSet$MuxingAttributeNameEnumeration(this);
    }
    
    public boolean containsAttribute(Object name, Object value) {
        return value.equals(getAttribute(name));
    }
    
    public boolean containsAttributes(AttributeSet attrs) {
        boolean result = true;
        Enumeration names = attrs.getAttributeNames();
        while (result && names.hasMoreElements()) {
            Object name = names.nextElement();
            result = attrs.getAttribute(name).equals(getAttribute(name));
        }
        return result;
    }
    
    public AttributeSet getResolveParent() {
        return null;
    }
    private AttributeSet[] attrs;
    {
    }
}
