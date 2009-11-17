package java.util;

import java.io.*;

class IdentityHashMap$KeySet extends AbstractSet {
    
    /*synthetic*/ IdentityHashMap$KeySet(IdentityHashMap x0, java.util.IdentityHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final IdentityHashMap this$0;
    
    private IdentityHashMap$KeySet(/*synthetic*/ final IdentityHashMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new IdentityHashMap$KeyIterator(this$0, null);
    }
    
    public int size() {
        return IdentityHashMap.access$000(this$0);
    }
    
    public boolean contains(Object o) {
        return this$0.containsKey(o);
    }
    
    public boolean remove(Object o) {
        int oldSize = IdentityHashMap.access$000(this$0);
        this$0.remove(o);
        return IdentityHashMap.access$000(this$0) != oldSize;
    }
    
    public boolean removeAll(Collection c) {
        boolean modified = false;
        for (Iterator i = iterator(); i.hasNext(); ) {
            if (c.contains(i.next())) {
                i.remove();
                modified = true;
            }
        }
        return modified;
    }
    
    public void clear() {
        this$0.clear();
    }
    
    public int hashCode() {
        int result = 0;
        for (Iterator i$ = this.iterator(); i$.hasNext(); ) {
            Object key = (Object)i$.next();
            result += System.identityHashCode(key);
        }
        return result;
    }
}
