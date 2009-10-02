package java.io;

import java.lang.reflect.Field;

public class ObjectStreamField implements Comparable {
    private final String name;
    private final String signature;
    private final Class type;
    private final boolean unshared;
    private final Field field;
    private int offset = 0;
    
    public ObjectStreamField(String name, Class type) {
        this(name, type, false);
    }
    
    public ObjectStreamField(String name, Class type, boolean unshared) {
        
        if (name == null) {
            throw new NullPointerException();
        }
        this.name = name;
        this.type = type;
        this.unshared = unshared;
        signature = ObjectStreamClass.getClassSignature(type).intern();
        field = null;
    }
    
    ObjectStreamField(String name, String signature, boolean unshared) {
        
        if (name == null) {
            throw new NullPointerException();
        }
        this.name = name;
        this.signature = signature.intern();
        this.unshared = unshared;
        field = null;
        switch (signature.charAt(0)) {
        case 'Z': 
            type = Boolean.TYPE;
            break;
        
        case 'B': 
            type = Byte.TYPE;
            break;
        
        case 'C': 
            type = Character.TYPE;
            break;
        
        case 'S': 
            type = Short.TYPE;
            break;
        
        case 'I': 
            type = Integer.TYPE;
            break;
        
        case 'J': 
            type = Long.TYPE;
            break;
        
        case 'F': 
            type = Float.TYPE;
            break;
        
        case 'D': 
            type = Double.TYPE;
            break;
        
        case 'L': 
        
        case '[': 
            type = Object.class;
            break;
        
        default: 
            throw new IllegalArgumentException("illegal signature");
        
        }
    }
    
    ObjectStreamField(Field field, boolean unshared, boolean showType) {
        
        this.field = field;
        this.unshared = unshared;
        name = field.getName();
        Class ftype = field.getType();
        type = (showType || ftype.isPrimitive()) ? ftype : Object.class;
        signature = ObjectStreamClass.getClassSignature(ftype).intern();
    }
    
    public String getName() {
        return name;
    }
    
    public Class getType() {
        return type;
    }
    
    public char getTypeCode() {
        return signature.charAt(0);
    }
    
    public String getTypeString() {
        return isPrimitive() ? null : signature;
    }
    
    public int getOffset() {
        return offset;
    }
    
    protected void setOffset(int offset) {
        this.offset = offset;
    }
    
    public boolean isPrimitive() {
        char tcode = signature.charAt(0);
        return ((tcode != 'L') && (tcode != '['));
    }
    
    public boolean isUnshared() {
        return unshared;
    }
    
    public int compareTo(Object obj) {
        ObjectStreamField other = (ObjectStreamField)(ObjectStreamField)obj;
        boolean isPrim = isPrimitive();
        if (isPrim != other.isPrimitive()) {
            return isPrim ? -1 : 1;
        }
        return name.compareTo(other.name);
    }
    
    public String toString() {
        return signature + ' ' + name;
    }
    
    Field getField() {
        return field;
    }
    
    String getSignature() {
        return signature;
    }
}
