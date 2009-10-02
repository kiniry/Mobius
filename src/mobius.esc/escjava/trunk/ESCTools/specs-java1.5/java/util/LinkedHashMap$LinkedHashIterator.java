package java.util;

import java.io.*;

abstract class LinkedHashMap$LinkedHashIterator implements Iterator {
    
    /*synthetic*/ LinkedHashMap$LinkedHashIterator(LinkedHashMap x0, java.util.LinkedHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final LinkedHashMap this$0;
    
    private LinkedHashMap$LinkedHashIterator(/*synthetic*/ final LinkedHashMap this$0) {
        this.this$0 = this$0;
        
    }
    LinkedHashMap$Entry nextEntry = LinkedHashMap.access$100(this$0).after;
    LinkedHashMap$Entry lastReturned = null;
    int expectedModCount = this$0.modCount;
    
    public boolean hasNext() {
        return nextEntry != LinkedHashMap.access$100(this$0);
    }
    
    public void remove() {
        if (lastReturned == null) throw new IllegalStateException();
        if (this$0.modCount != expectedModCount) throw new ConcurrentModificationException();
        this$0.remove(lastReturned.key);
        lastReturned = null;
        expectedModCount = this$0.modCount;
    }
    
    LinkedHashMap$Entry nextEntry() {
        if (this$0.modCount != expectedModCount) throw new ConcurrentModificationException();
        if (nextEntry == LinkedHashMap.access$100(this$0)) throw new NoSuchElementException();
        LinkedHashMap$Entry e = lastReturned = nextEntry;
        nextEntry = e.after;
        return e;
    }
}
