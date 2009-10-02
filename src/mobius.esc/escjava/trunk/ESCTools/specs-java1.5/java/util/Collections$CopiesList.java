package java.util;

import java.io.Serializable;

class Collections$CopiesList extends AbstractList implements RandomAccess, Serializable {
    static final long serialVersionUID = 2739099268398711800L;
    int n;
    Object element;
    
    Collections$CopiesList(int n, Object o) {
        
        if (n < 0) throw new IllegalArgumentException("List length = " + n);
        this.n = n;
        element = o;
    }
    
    public int size() {
        return n;
    }
    
    public boolean contains(Object obj) {
        return n != 0 && Collections.access$000(obj, element);
    }
    
    public Object get(int index) {
        if (index < 0 || index >= n) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + n);
        return element;
    }
}
