package java.util;

import java.io.*;

class HashMap$Values extends AbstractCollection {
    
    /*synthetic*/ HashMap$Values(HashMap x0, java.util.HashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final HashMap this$0;
    
    private HashMap$Values(/*synthetic*/ final HashMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return this$0.newValueIterator();
    }
    
    public int size() {
        return this$0.size;
    }
    
    public boolean contains(Object o) {
        return this$0.containsValue(o);
    }
    
    public void clear() {
        this$0.clear();
    }
}
