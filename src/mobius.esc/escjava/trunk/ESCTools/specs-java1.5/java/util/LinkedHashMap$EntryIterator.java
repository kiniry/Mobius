package java.util;

import java.io.*;

class LinkedHashMap$EntryIterator extends LinkedHashMap$LinkedHashIterator {
    
    /*synthetic*/ LinkedHashMap$EntryIterator(LinkedHashMap x0, java.util.LinkedHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final LinkedHashMap this$0;
    
    private LinkedHashMap$EntryIterator(/*synthetic*/ final LinkedHashMap this$0) {
        super( this.this$0 = this$0, null);
    }
    
    public Map$Entry next() {
        return nextEntry();
    }
    
    /*synthetic public Object next() {
        return this.next();
    }*/
}
