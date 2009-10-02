package java.util;

import java.io.Serializable;

class Collections$EmptySet extends AbstractSet implements Serializable {
    
    /*synthetic*/ Collections$EmptySet(java.util.Collections$1 x0) {
        this();
    }
    
    private Collections$EmptySet() {
        //
    }
    private static final long serialVersionUID = 1582296315990362920L;
    
    public Iterator iterator() {
        return new Collections$EmptySet$1(this);
    }
    
    public int size() {
        return 0;
    }
    
    public boolean contains(Object obj) {
        return false;
    }
    
    private Object readResolve() {
        return Collections.EMPTY_SET;
    }
}
