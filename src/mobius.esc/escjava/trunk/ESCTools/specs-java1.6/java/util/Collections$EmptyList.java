package java.util;

import java.io.Serializable;

class Collections$EmptyList extends AbstractList implements RandomAccess, Serializable {
    
    /*synthetic*/ Collections$EmptyList(java.util.Collections$1 x0) {
        this();
    }
    
    private Collections$EmptyList() {
        
    }
    private static final long serialVersionUID = 8842843931221139166L;
    
    public int size() {
        return 0;
    }
    
    public boolean contains(Object obj) {
        return false;
    }
    
    public Object get(int index) {
        throw new IndexOutOfBoundsException("Index: " + index);
    }
    
    private Object readResolve() {
        return Collections.EMPTY_LIST;
    }
}
