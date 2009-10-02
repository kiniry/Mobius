package java.util;

import java.io.Serializable;

class Collections$SingletonSet extends AbstractSet implements Serializable {
    
    /*synthetic*/ static Object access$400(Collections$SingletonSet x0) {
        return x0.element;
    }
    private static final long serialVersionUID = 3193687207550431679L;
    private final Object element;
    
    Collections$SingletonSet(Object o) {
        
        element = o;
    }
    
    public Iterator iterator() {
        return new Collections$SingletonSet$1(this);
    }
    
    public int size() {
        return 1;
    }
    
    public boolean contains(Object o) {
        return Collections.access$000(o, element);
    }
}
