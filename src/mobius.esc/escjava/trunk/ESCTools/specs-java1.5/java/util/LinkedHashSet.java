package java.util;

public class LinkedHashSet extends HashSet implements Set, Cloneable, java.io.Serializable {
    private static final long serialVersionUID = -2851667679971038690L;
    
    public LinkedHashSet(int initialCapacity, float loadFactor) {
        super(initialCapacity, loadFactor, true);
    }
    
    public LinkedHashSet(int initialCapacity) {
        super(initialCapacity, 0.75F, true);
    }
    
    public LinkedHashSet() {
        super(16, 0.75F, true);
    }
    
    public LinkedHashSet(Collection c) {
        super(Math.max(2 * c.size(), 11), 0.75F, true);
        addAll(c);
    }
}
