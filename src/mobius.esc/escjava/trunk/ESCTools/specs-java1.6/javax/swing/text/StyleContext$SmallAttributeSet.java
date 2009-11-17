package javax.swing.text;

import java.awt.*;
import java.util.*;
import java.io.*;

public class StyleContext$SmallAttributeSet implements AttributeSet {
    /*synthetic*/ final StyleContext this$0;
    
    public StyleContext$SmallAttributeSet(/*synthetic*/ final StyleContext this$0, Object[] attributes) {
        this.this$0 = this$0;
        
        this.attributes = attributes;
        updateResolveParent();
    }
    
    public StyleContext$SmallAttributeSet(/*synthetic*/ final StyleContext this$0, AttributeSet attrs) {
        this.this$0 = this$0;
        
        int n = attrs.getAttributeCount();
        Object[] tbl = new Object[2 * n];
        Enumeration names = attrs.getAttributeNames();
        int i = 0;
        while (names.hasMoreElements()) {
            tbl[i] = names.nextElement();
            tbl[i + 1] = attrs.getAttribute(tbl[i]);
            i += 2;
        }
        attributes = tbl;
        updateResolveParent();
    }
    
    private void updateResolveParent() {
        resolveParent = null;
        Object[] tbl = attributes;
        for (int i = 0; i < tbl.length; i += 2) {
            if (tbl[i] == StyleConstants.ResolveAttribute) {
                resolveParent = (AttributeSet)(AttributeSet)tbl[i + 1];
                break;
            }
        }
    }
    
    Object getLocalAttribute(Object nm) {
        if (nm == StyleConstants.ResolveAttribute) {
            return resolveParent;
        }
        Object[] tbl = attributes;
        for (int i = 0; i < tbl.length; i += 2) {
            if (nm.equals(tbl[i])) {
                return tbl[i + 1];
            }
        }
        return null;
    }
    
    public String toString() {
        String s = "{";
        Object[] tbl = attributes;
        for (int i = 0; i < tbl.length; i += 2) {
            if (tbl[i + 1] instanceof AttributeSet) {
                s = s + tbl[i] + "=" + "AttributeSet" + ",";
            } else {
                s = s + tbl[i] + "=" + tbl[i + 1] + ",";
            }
        }
        s = s + "}";
        return s;
    }
    
    public int hashCode() {
        int code = 0;
        Object[] tbl = attributes;
        for (int i = 1; i < tbl.length; i += 2) {
            code ^= tbl[i].hashCode();
        }
        return code;
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof AttributeSet) {
            AttributeSet attrs = (AttributeSet)(AttributeSet)obj;
            return ((getAttributeCount() == attrs.getAttributeCount()) && containsAttributes(attrs));
        }
        return false;
    }
    
    public Object clone() {
        return this;
    }
    
    public int getAttributeCount() {
        return attributes.length / 2;
    }
    
    public boolean isDefined(Object key) {
        Object[] a = attributes;
        int n = a.length;
        for (int i = 0; i < n; i += 2) {
            if (key.equals(a[i])) {
                return true;
            }
        }
        return false;
    }
    
    public boolean isEqual(AttributeSet attr) {
        if (attr instanceof StyleContext$SmallAttributeSet) {
            return attr == this;
        }
        return ((getAttributeCount() == attr.getAttributeCount()) && containsAttributes(attr));
    }
    
    public AttributeSet copyAttributes() {
        return this;
    }
    
    public Object getAttribute(Object key) {
        Object value = getLocalAttribute(key);
        if (value == null) {
            AttributeSet parent = getResolveParent();
            if (parent != null) value = parent.getAttribute(key);
        }
        return value;
    }
    
    public Enumeration getAttributeNames() {
        return new StyleContext$KeyEnumeration(this$0, attributes);
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
        return resolveParent;
    }
    Object[] attributes;
    AttributeSet resolveParent;
}
