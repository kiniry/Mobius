package java.util;

import java.lang.reflect.*;

class Arrays$ArrayList extends AbstractList implements RandomAccess, java.io.Serializable {
    private static final long serialVersionUID = -2764017481108945198L;
    private Object[] a;
    
    Arrays$ArrayList(Object[] array) {
        
        if (array == null) throw new NullPointerException();
        a = array;
    }
    
    public int size() {
        return a.length;
    }
    
    public Object[] toArray() {
        return (Object[])(Object[])a.clone();
    }
    
    public Object get(int index) {
        return (Object)a[index];
    }
    
    public Object set(int index, Object element) {
        Object oldValue = a[index];
        a[index] = element;
        return (Object)oldValue;
    }
    
    public int indexOf(Object o) {
        if (o == null) {
            for (int i = 0; i < a.length; i++) if (a[i] == null) return i;
        } else {
            for (int i = 0; i < a.length; i++) if (o.equals(a[i])) return i;
        }
        return -1;
    }
    
    public boolean contains(Object o) {
        return indexOf(o) != -1;
    }
}
