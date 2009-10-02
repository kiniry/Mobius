package java.util;

import java.io.Serializable;
import java.lang.reflect.Array;

class Collections$CheckedCollection implements Collection, Serializable {
    private static final long serialVersionUID = 1578914078182001775L;
    final Collection c;
    final Class type;
    
    void typeCheck(Object o) {
        if (!type.isInstance(o)) throw new ClassCastException("Attempt to insert " + o.getClass() + " element into collection with element type " + type);
    }
    
    Collections$CheckedCollection(Collection c, Class type) {
        
        if (c == null || type == null) throw new NullPointerException();
        this.c = c;
        this.type = type;
    }
    
    public int size() {
        return c.size();
    }
    
    public boolean isEmpty() {
        return c.isEmpty();
    }
    
    public boolean contains(Object o) {
        return c.contains(o);
    }
    
    public Object[] toArray() {
        return c.toArray();
    }
    
    public Object[] toArray(Object[] a) {
        return c.toArray(a);
    }
    
    public String toString() {
        return c.toString();
    }
    
    public boolean remove(Object o) {
        return c.remove(o);
    }
    
    public boolean containsAll(Collection coll) {
        return c.containsAll(coll);
    }
    
    public boolean removeAll(Collection coll) {
        return c.removeAll(coll);
    }
    
    public boolean retainAll(Collection coll) {
        return c.retainAll(coll);
    }
    
    public void clear() {
        c.clear();
    }
    
    public Iterator iterator() {
        return new Collections$CheckedCollection$1(this);
    }
    
    public boolean add(Object o) {
        typeCheck(o);
        return c.add(o);
    }
    
    public boolean addAll(Collection coll) {
        Object[] a = null;
        try {
            a = coll.toArray(zeroLengthElementArray());
        } catch (ArrayStoreException e) {
            throw new ClassCastException();
        }
        boolean result = false;
        for (Object[] arr$ = a, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            Object e = arr$[i$];
            result |= c.add(e);
        }
        return result;
    }
    private Object[] zeroLengthElementArray = null;
    
    Object[] zeroLengthElementArray() {
        if (zeroLengthElementArray == null) zeroLengthElementArray = (Object[])(Object[])Array.newInstance(type, 0);
        return zeroLengthElementArray;
    }
}
