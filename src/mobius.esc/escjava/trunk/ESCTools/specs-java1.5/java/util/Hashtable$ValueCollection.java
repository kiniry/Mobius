package java.util;

import java.io.*;

class Hashtable$ValueCollection extends AbstractCollection {
    
    /*synthetic*/ Hashtable$ValueCollection(Hashtable x0, java.util.Hashtable$1 x1) {
        this(x0);
    }
    /*synthetic*/ final Hashtable this$0;
    
    private Hashtable$ValueCollection(/*synthetic*/ final Hashtable this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return Hashtable.access$100(this$0, 1);
    }
    
    public int size() {
        return Hashtable.access$200(this$0);
    }
    
    public boolean contains(Object o) {
        return this$0.containsValue(o);
    }
    
    public void clear() {
        this$0.clear();
    }
}
