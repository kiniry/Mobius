package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

final class ConcurrentHashMap$EntrySet extends AbstractSet {
    /*synthetic*/ final ConcurrentHashMap this$0;
    
    ConcurrentHashMap$EntrySet(/*synthetic*/ final ConcurrentHashMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new ConcurrentHashMap$EntryIterator(this$0);
    }
    
    public boolean contains(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry e = (Map$Entry)(Map$Entry)o;
        Object v = this$0.get(e.getKey());
        return v != null && v.equals(e.getValue());
    }
    
    public boolean remove(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry e = (Map$Entry)(Map$Entry)o;
        return this$0.remove(e.getKey(), e.getValue());
    }
    
    public int size() {
        return this$0.size();
    }
    
    public void clear() {
        this$0.clear();
    }
    
    public Object[] toArray() {
        Collection c = new ArrayList(size());
        for (Iterator i = iterator(); i.hasNext(); ) c.add(new ConcurrentHashMap$SimpleEntry((Map$Entry)i.next()));
        return c.toArray();
    }
    
    public Object[] toArray(Object[] a) {
        Collection c = new ArrayList(size());
        for (Iterator i = iterator(); i.hasNext(); ) c.add(new ConcurrentHashMap$SimpleEntry((Map$Entry)i.next()));
        return c.toArray(a);
    }
}
