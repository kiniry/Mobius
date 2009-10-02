package java.util;

import java.io.Serializable;

class Collections$UnmodifiableSet extends Collections$UnmodifiableCollection implements Set, Serializable {
    private static final long serialVersionUID = -9215047833775013803L;
    
    Collections$UnmodifiableSet(Set s) {
        super(s);
    }
    
    public boolean equals(Object o) {
        return c.equals(o);
    }
    
    public int hashCode() {
        return c.hashCode();
    }
}
