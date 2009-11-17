package java.util;

import java.io.Serializable;

class Collections$SingletonList extends AbstractList implements RandomAccess, Serializable {
    static final long serialVersionUID = 3093736618740652951L;
    private final Object element;
    
    Collections$SingletonList(Object obj) {
        
        element = obj;
    }
    
    public int size() {
        return 1;
    }
    
    public boolean contains(Object obj) {
        return Collections.access$000(obj, element);
    }
    
    public Object get(int index) {
        if (index != 0) throw new IndexOutOfBoundsException("Index: " + index + ", Size: 1");
        return element;
    }
}
