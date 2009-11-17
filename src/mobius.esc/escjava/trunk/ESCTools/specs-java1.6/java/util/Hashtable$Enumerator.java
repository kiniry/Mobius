package java.util;

import java.io.*;

class Hashtable$Enumerator implements Enumeration, Iterator {
    /*synthetic*/ final Hashtable this$0;
    Hashtable$Entry[] table = Hashtable.access$400(this$0);
    int index = table.length;
    Hashtable$Entry entry = null;
    Hashtable$Entry lastReturned = null;
    int type;
    boolean iterator;
    protected int expectedModCount = Hashtable.access$500(this$0);
    
    Hashtable$Enumerator(/*synthetic*/ final Hashtable this$0, int type, boolean iterator) {
        this.this$0 = this$0;
        
        this.type = type;
        this.iterator = iterator;
    }
    
    public boolean hasMoreElements() {
        Hashtable$Entry e = entry;
        int i = index;
        Hashtable$Entry[] t = table;
        while (e == null && i > 0) {
            e = t[--i];
        }
        entry = e;
        index = i;
        return e != null;
    }
    
    public Object nextElement() {
        Hashtable$Entry et = entry;
        int i = index;
        Hashtable$Entry[] t = table;
        while (et == null && i > 0) {
            et = t[--i];
        }
        entry = et;
        index = i;
        if (et != null) {
            Hashtable$Entry e = lastReturned = entry;
            entry = e.next;
            return type == 0 ? (Object)e.key : (type == 1 ? (Object)e.value : (Object)e);
        }
        throw new NoSuchElementException("Hashtable Enumerator");
    }
    
    public boolean hasNext() {
        return hasMoreElements();
    }
    
    public Object next() {
        if (Hashtable.access$500(this$0) != expectedModCount) throw new ConcurrentModificationException();
        return nextElement();
    }
    
    public void remove() {
        if (!iterator) throw new UnsupportedOperationException();
        if (lastReturned == null) throw new IllegalStateException("Hashtable Enumerator");
        if (Hashtable.access$500(this$0) != expectedModCount) throw new ConcurrentModificationException();
        synchronized (this$0) {
            Hashtable$Entry[] tab = Hashtable.access$400(this$0);
            int index = (lastReturned.hash & 2147483647) % tab.length;
            for (Hashtable$Entry e = tab[index], prev = null; e != null; prev = e, e = e.next) {
                if (e == lastReturned) {
                    Hashtable.access$508(this$0);
                    expectedModCount++;
                    if (prev == null) tab[index] = e.next; else prev.next = e.next;
                    Hashtable.access$210(this$0);
                    lastReturned = null;
                    return;
                }
            }
            throw new ConcurrentModificationException();
        }
    }
}
