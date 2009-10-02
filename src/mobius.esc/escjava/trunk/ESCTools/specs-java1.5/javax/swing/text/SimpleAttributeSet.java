package javax.swing.text;

import java.util.Hashtable;
import java.util.Enumeration;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.Serializable;

public class SimpleAttributeSet implements MutableAttributeSet, Serializable, Cloneable {
    
    /*synthetic*/ static Enumeration access$000() {
        return getEmptyEnumeration();
    }
    public static final AttributeSet EMPTY = new SimpleAttributeSet$EmptyAttributeSet();
    private transient Hashtable table = new Hashtable(3);
    private static Enumeration emptyEnumeration;
    
    public SimpleAttributeSet() {
        
    }
    
    public SimpleAttributeSet(AttributeSet source) {
        
        addAttributes(source);
    }
    
    private SimpleAttributeSet(Hashtable table) {
        
        this.table = table;
    }
    
    public boolean isEmpty() {
        return table.isEmpty();
    }
    
    public int getAttributeCount() {
        return table.size();
    }
    
    public boolean isDefined(Object attrName) {
        return table.containsKey(attrName);
    }
    
    public boolean isEqual(AttributeSet attr) {
        return ((getAttributeCount() == attr.getAttributeCount()) && containsAttributes(attr));
    }
    
    public AttributeSet copyAttributes() {
        return (AttributeSet)(AttributeSet)clone();
    }
    
    public Enumeration getAttributeNames() {
        return table.keys();
    }
    
    public Object getAttribute(Object name) {
        Object value = table.get(name);
        if (value == null) {
            AttributeSet parent = getResolveParent();
            if (parent != null) {
                value = parent.getAttribute(name);
            }
        }
        return value;
    }
    
    public boolean containsAttribute(Object name, Object value) {
        return value.equals(getAttribute(name));
    }
    
    public boolean containsAttributes(AttributeSet attributes) {
        boolean result = true;
        Enumeration names = attributes.getAttributeNames();
        while (result && names.hasMoreElements()) {
            Object name = names.nextElement();
            result = attributes.getAttribute(name).equals(getAttribute(name));
        }
        return result;
    }
    
    public void addAttribute(Object name, Object value) {
        table.put(name, value);
    }
    
    public void addAttributes(AttributeSet attributes) {
        Enumeration names = attributes.getAttributeNames();
        while (names.hasMoreElements()) {
            Object name = names.nextElement();
            addAttribute(name, attributes.getAttribute(name));
        }
    }
    
    public void removeAttribute(Object name) {
        table.remove(name);
    }
    
    public void removeAttributes(Enumeration names) {
        while (names.hasMoreElements()) removeAttribute(names.nextElement());
    }
    
    public void removeAttributes(AttributeSet attributes) {
        if (attributes == this) {
            table.clear();
        } else {
            Enumeration names = attributes.getAttributeNames();
            while (names.hasMoreElements()) {
                Object name = names.nextElement();
                Object value = attributes.getAttribute(name);
                if (value.equals(getAttribute(name))) removeAttribute(name);
            }
        }
    }
    
    public AttributeSet getResolveParent() {
        return (AttributeSet)(AttributeSet)table.get(StyleConstants.ResolveAttribute);
    }
    
    public void setResolveParent(AttributeSet parent) {
        addAttribute(StyleConstants.ResolveAttribute, parent);
    }
    
    public Object clone() {
        SimpleAttributeSet attr;
        try {
            attr = (SimpleAttributeSet)(SimpleAttributeSet)super.clone();
            attr.table = (Hashtable)(Hashtable)table.clone();
        } catch (CloneNotSupportedException cnse) {
            attr = null;
        }
        return attr;
    }
    
    public int hashCode() {
        return table.hashCode();
    }
    
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj instanceof AttributeSet) {
            AttributeSet attrs = (AttributeSet)(AttributeSet)obj;
            return isEqual(attrs);
        }
        return false;
    }
    
    public String toString() {
        String s = "";
        Enumeration names = getAttributeNames();
        while (names.hasMoreElements()) {
            Object key = names.nextElement();
            Object value = getAttribute(key);
            if (value instanceof AttributeSet) {
                s = s + key + "=**AttributeSet** ";
            } else {
                s = s + key + "=" + value + " ";
            }
        }
        return s;
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        StyleContext.writeAttributeSet(s, this);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        table = new Hashtable(3);
        StyleContext.readAttributeSet(s, this);
    }
    {
    }
    {
    }
    
    private static Enumeration getEmptyEnumeration() {
        if (emptyEnumeration == null) {
            emptyEnumeration = new SimpleAttributeSet$1();
        }
        return emptyEnumeration;
    }
}
