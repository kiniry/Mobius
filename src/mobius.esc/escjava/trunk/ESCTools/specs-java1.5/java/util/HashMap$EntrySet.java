package java.util;

import java.io.*;

class HashMap$EntrySet extends AbstractSet {
    
    /*synthetic*/ HashMap$EntrySet(HashMap x0, java.util.HashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final HashMap this$0;
    
    private HashMap$EntrySet(/*synthetic*/ final HashMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return this$0.newEntryIterator();
    }
    
    public boolean contains(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry e = (Map$Entry)(Map$Entry)o;
        HashMap$Entry candidate = this$0.getEntry(e.getKey());
        return candidate != null && candidate.equals(e);
    }
    
    public boolean remove(Object o) {
        return this$0.removeMapping(o) != null;
    }
    
    public int size() {
        return this$0.size;
    }
    
    public void clear() {
        this$0.clear();
    }
}
