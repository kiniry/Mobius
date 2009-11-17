package java.util;

import java.io.*;

class Hashtable$EntrySet extends AbstractSet {
    
    /*synthetic*/ Hashtable$EntrySet(Hashtable x0, java.util.Hashtable$1 x1) {
        this(x0);
    }
    /*synthetic*/ final Hashtable this$0;
    
    private Hashtable$EntrySet(/*synthetic*/ final Hashtable this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return Hashtable.access$100(this$0, 2);
    }
    
    public boolean add(Object o) {
        return super.add(o);
    }
    
    public boolean contains(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry entry = (Map$Entry)(Map$Entry)o;
        Object key = entry.getKey();
        Hashtable$Entry[] tab = Hashtable.access$400(this$0);
        int hash = key.hashCode();
        int index = (hash & 2147483647) % tab.length;
        for (Hashtable$Entry e = tab[index]; e != null; e = e.next) if (e.hash == hash && e.equals(entry)) return true;
        return false;
    }
    
    public boolean remove(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry entry = (Map$Entry)(Map$Entry)o;
        Object key = entry.getKey();
        Hashtable$Entry[] tab = Hashtable.access$400(this$0);
        int hash = key.hashCode();
        int index = (hash & 2147483647) % tab.length;
        for (Hashtable$Entry e = tab[index], prev = null; e != null; prev = e, e = e.next) {
            if (e.hash == hash && e.equals(entry)) {
                Hashtable.access$508(this$0);
                if (prev != null) prev.next = e.next; else tab[index] = e.next;
                Hashtable.access$210(this$0);
                e.value = null;
                return true;
            }
        }
        return false;
    }
    
    public int size() {
        return Hashtable.access$200(this$0);
    }
    
    public void clear() {
        this$0.clear();
    }
}
