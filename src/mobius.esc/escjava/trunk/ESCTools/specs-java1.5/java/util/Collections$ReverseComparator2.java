package java.util;

import java.io.Serializable;

class Collections$ReverseComparator2 implements Comparator, Serializable {
    /*synthetic*/ static final boolean $assertionsDisabled = !Collections.class.desiredAssertionStatus();
    private static final long serialVersionUID = 4374092139857L;
    private Comparator cmp;
    
    Collections$ReverseComparator2(Comparator cmp) {
        
        if (!$assertionsDisabled && !(cmp != null)) throw new AssertionError();
        this.cmp = cmp;
    }
    
    public int compare(Object t1, Object t2) {
        return cmp.compare(t2, t1);
    }
}
