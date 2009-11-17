package java.util;

import java.io.*;

class HashMap$KeySet extends AbstractSet {
    
    /*synthetic*/ HashMap$KeySet(HashMap x0, java.util.HashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final HashMap this$0;
    
    private HashMap$KeySet(/*synthetic*/ final HashMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return this$0.newKeyIterator();
    }
    
    public int size() {
        return this$0.size;
    }
    
    public boolean contains(Object o) {
        return this$0.containsKey(o);
    }
    
    public boolean remove(Object o) {
        return this$0.removeEntryForKey(o) != null;
    }
    
    public void clear() {
        this$0.clear();
    }
}
