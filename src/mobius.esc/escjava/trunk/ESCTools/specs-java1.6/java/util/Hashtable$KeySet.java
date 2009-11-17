package java.util;

import java.io.*;

class Hashtable$KeySet extends AbstractSet {
    
    /*synthetic*/ Hashtable$KeySet(Hashtable x0, java.util.Hashtable$1 x1) {
        this(x0);
    }
    /*synthetic*/ final Hashtable this$0;
    
    private Hashtable$KeySet(/*synthetic*/ final Hashtable this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return Hashtable.access$100(this$0, 0);
    }
    
    public int size() {
        return Hashtable.access$200(this$0);
    }
    
    public boolean contains(Object o) {
        return this$0.containsKey(o);
    }
    
    public boolean remove(Object o) {
        return this$0.remove(o) != null;
    }
    
    public void clear() {
        this$0.clear();
    }
}
