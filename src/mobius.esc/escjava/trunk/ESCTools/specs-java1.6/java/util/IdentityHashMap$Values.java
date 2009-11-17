package java.util;

import java.io.*;

class IdentityHashMap$Values extends AbstractCollection {
    
    /*synthetic*/ IdentityHashMap$Values(IdentityHashMap x0, java.util.IdentityHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final IdentityHashMap this$0;
    
    private IdentityHashMap$Values(/*synthetic*/ final IdentityHashMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new IdentityHashMap$ValueIterator(this$0, null);
    }
    
    public int size() {
        return IdentityHashMap.access$000(this$0);
    }
    
    public boolean contains(Object o) {
        return this$0.containsValue(o);
    }
    
    public boolean remove(Object o) {
        for (Iterator i = iterator(); i.hasNext(); ) {
            if (i.next() == o) {
                i.remove();
                return true;
            }
        }
        return false;
    }
    
    public void clear() {
        this$0.clear();
    }
}
