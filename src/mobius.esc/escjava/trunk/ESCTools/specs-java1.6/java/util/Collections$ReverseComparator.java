package java.util;

import java.io.Serializable;

class Collections$ReverseComparator implements Comparator, Serializable {
    
    /*synthetic*/ Collections$ReverseComparator(java.util.Collections$1 x0) {
        this();
    }
    
    private Collections$ReverseComparator() {
        
    }
    private static final long serialVersionUID = 7207038068494060240L;
    
    public int compare(Comparable c1, Comparable c2) {
        return c2.compareTo(c1);
    }
    
    /*synthetic*/ public int compare(Object x0, Object x1) {
        return this.compare((Comparable)x0, (Comparable)x1);
    }
}
