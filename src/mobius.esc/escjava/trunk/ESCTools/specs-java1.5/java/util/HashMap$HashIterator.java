package java.util;

import java.io.*;

abstract class HashMap$HashIterator implements Iterator {
    /*synthetic*/ final HashMap this$0;
    HashMap$Entry next;
    int expectedModCount;
    int index;
    HashMap$Entry current;
    
    HashMap$HashIterator(/*synthetic*/ final HashMap this$0) {
        this.this$0 = this$0;
        
        expectedModCount = this$0.modCount;
        HashMap$Entry[] t = this$0.table;
        int i = t.length;
        HashMap$Entry n = null;
        if (this$0.size != 0) {
            while (i > 0 && (n = t[--i]) == null) ;
        }
        next = n;
        index = i;
    }
    
    public boolean hasNext() {
        return next != null;
    }
    
    HashMap$Entry nextEntry() {
        if (this$0.modCount != expectedModCount) throw new ConcurrentModificationException();
        HashMap$Entry e = next;
        if (e == null) throw new NoSuchElementException();
        HashMap$Entry n = e.next;
        HashMap$Entry[] t = this$0.table;
        int i = index;
        while (n == null && i > 0) n = t[--i];
        index = i;
        next = n;
        return current = e;
    }
    
    public void remove() {
        if (current == null) throw new IllegalStateException();
        if (this$0.modCount != expectedModCount) throw new ConcurrentModificationException();
        Object k = current.key;
        current = null;
        this$0.removeEntryForKey(k);
        expectedModCount = this$0.modCount;
    }
}
