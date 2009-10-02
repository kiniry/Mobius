package java.util;

import java.io.Serializable;

class Collections$CheckedSet extends Collections$CheckedCollection implements Set, Serializable {
    private static final long serialVersionUID = 4694047833775013803L;
    
    Collections$CheckedSet(Set s, Class elementType) {
        super(s, elementType);
    }
    
    public boolean equals(Object o) {
        return c.equals(o);
    }
    
    public int hashCode() {
        return c.hashCode();
    }
}
