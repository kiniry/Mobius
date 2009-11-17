package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

final class ConcurrentHashMap$Values extends AbstractCollection {
    /*synthetic*/ final ConcurrentHashMap this$0;
    
    ConcurrentHashMap$Values(/*synthetic*/ final ConcurrentHashMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new ConcurrentHashMap$ValueIterator(this$0);
    }
    
    public int size() {
        return this$0.size();
    }
    
    public boolean contains(Object o) {
        return this$0.containsValue(o);
    }
    
    public void clear() {
        this$0.clear();
    }
    
    public Object[] toArray() {
        Collection c = new ArrayList();
        for (Iterator i = iterator(); i.hasNext(); ) c.add(i.next());
        return c.toArray();
    }
    
    public Object[] toArray(Object[] a) {
        Collection c = new ArrayList();
        for (Iterator i = iterator(); i.hasNext(); ) c.add(i.next());
        return c.toArray(a);
    }
}
