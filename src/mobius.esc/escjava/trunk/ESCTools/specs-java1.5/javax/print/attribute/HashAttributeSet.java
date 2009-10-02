package javax.print.attribute;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.HashMap;

public class HashAttributeSet implements AttributeSet, Serializable {
    private static final long serialVersionUID = 5311560590283707917L;
    private Class myInterface;
    private transient HashMap attrMap = new HashMap();
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        Attribute[] attrs = toArray();
        s.writeInt(attrs.length);
        for (int i = 0; i < attrs.length; i++) {
            s.writeObject(attrs[i]);
        }
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        attrMap = new HashMap();
        int count = s.readInt();
        Attribute attr;
        for (int i = 0; i < count; i++) {
            attr = (Attribute)(Attribute)s.readObject();
            add(attr);
        }
    }
    
    public HashAttributeSet() {
        this(Attribute.class);
    }
    
    public HashAttributeSet(Attribute attribute) {
        this(attribute, Attribute.class);
    }
    
    public HashAttributeSet(Attribute[] attributes) {
        this(attributes, Attribute.class);
    }
    
    public HashAttributeSet(AttributeSet attributes) {
        this(attributes, Attribute.class);
    }
    
    protected HashAttributeSet(Class interfaceName) {
        
        if (interfaceName == null) {
            throw new NullPointerException("null interface");
        }
        myInterface = interfaceName;
    }
    
    protected HashAttributeSet(Attribute attribute, Class interfaceName) {
        
        if (interfaceName == null) {
            throw new NullPointerException("null interface");
        }
        myInterface = interfaceName;
        add(attribute);
    }
    
    protected HashAttributeSet(Attribute[] attributes, Class interfaceName) {
        
        if (interfaceName == null) {
            throw new NullPointerException("null interface");
        }
        myInterface = interfaceName;
        int n = attributes == null ? 0 : attributes.length;
        for (int i = 0; i < n; ++i) {
            add(attributes[i]);
        }
    }
    
    protected HashAttributeSet(AttributeSet attributes, Class interfaceName) {
        
        myInterface = interfaceName;
        if (attributes != null) {
            Attribute[] attribArray = attributes.toArray();
            int n = attribArray == null ? 0 : attribArray.length;
            for (int i = 0; i < n; ++i) {
                add(attribArray[i]);
            }
        }
    }
    
    public Attribute get(Class category) {
        return (Attribute)(Attribute)attrMap.get(AttributeSetUtilities.verifyAttributeCategory(category, Attribute.class));
    }
    
    public boolean add(Attribute attribute) {
        Object oldAttribute = attrMap.put(attribute.getCategory(), AttributeSetUtilities.verifyAttributeValue(attribute, myInterface));
        return (!attribute.equals(oldAttribute));
    }
    
    public boolean remove(Class category) {
        return category != null && AttributeSetUtilities.verifyAttributeCategory(category, Attribute.class) != null && attrMap.remove(category) != null;
    }
    
    public boolean remove(Attribute attribute) {
        return attribute != null && attrMap.remove(attribute.getCategory()) != null;
    }
    
    public boolean containsKey(Class category) {
        return category != null && AttributeSetUtilities.verifyAttributeCategory(category, Attribute.class) != null && attrMap.get(category) != null;
    }
    
    public boolean containsValue(Attribute attribute) {
        return attribute != null && attribute instanceof Attribute && attribute.equals(attrMap.get(((Attribute)attribute).getCategory()));
    }
    
    public boolean addAll(AttributeSet attributes) {
        Attribute[] attrs = attributes.toArray();
        boolean result = false;
        for (int i = 0; i < attrs.length; i++) {
            Attribute newValue = AttributeSetUtilities.verifyAttributeValue(attrs[i], myInterface);
            Object oldValue = attrMap.put(newValue.getCategory(), newValue);
            result = (!newValue.equals(oldValue)) || result;
        }
        return result;
    }
    
    public int size() {
        return attrMap.size();
    }
    
    public Attribute[] toArray() {
        Attribute[] attrs = new Attribute[size()];
        attrMap.values().toArray(attrs);
        return attrs;
    }
    
    public void clear() {
        attrMap.clear();
    }
    
    public boolean isEmpty() {
        return attrMap.isEmpty();
    }
    
    public boolean equals(Object object) {
        if (object == null || !(object instanceof AttributeSet)) {
            return false;
        }
        AttributeSet aset = (AttributeSet)(AttributeSet)object;
        if (aset.size() != size()) {
            return false;
        }
        Attribute[] attrs = toArray();
        for (int i = 0; i < attrs.length; i++) {
            if (!aset.containsValue(attrs[i])) {
                return false;
            }
        }
        return true;
    }
    
    public int hashCode() {
        int hcode = 0;
        Attribute[] attrs = toArray();
        for (int i = 0; i < attrs.length; i++) {
            hcode += attrs[i].hashCode();
        }
        return hcode;
    }
}
