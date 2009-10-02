package java.util;

import java.io.*;

class IdentityHashMap$EntrySet extends AbstractSet {
    
    /*synthetic*/ IdentityHashMap$EntrySet(IdentityHashMap x0, java.util.IdentityHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final IdentityHashMap this$0;
    
    private IdentityHashMap$EntrySet(/*synthetic*/ final IdentityHashMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new IdentityHashMap$EntryIterator(this$0, null);
    }
    
    public boolean contains(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry entry = (Map$Entry)(Map$Entry)o;
        return IdentityHashMap.access$1300(this$0, entry.getKey(), entry.getValue());
    }
    
    public boolean remove(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry entry = (Map$Entry)(Map$Entry)o;
        return IdentityHashMap.access$1400(this$0, entry.getKey(), entry.getValue());
    }
    
    public int size() {
        return IdentityHashMap.access$000(this$0);
    }
    
    public void clear() {
        this$0.clear();
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
    
    public Object[] toArray() {
        List c = new ArrayList(size());
        for (Iterator i$ = this.iterator(); i$.hasNext(); ) {
            Map$Entry e = (Map$Entry)i$.next();
            c.add(new AbstractMap$SimpleEntry(e));
        }
        return c.toArray();
    }
    
    public Object[] toArray(Object[] a) {
        int size = size();
        if (a.length < size) a = (Object[])(Object[])java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), size);
        Iterator it = iterator();
        for (int i = 0; i < size; i++) a[i] = (Object)new AbstractMap$SimpleEntry((Map$Entry)it.next());
        if (a.length > size) a[size] = null;
        return a;
    }
}
