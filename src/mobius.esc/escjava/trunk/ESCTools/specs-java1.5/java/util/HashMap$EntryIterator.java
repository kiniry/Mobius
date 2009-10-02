package java.util;

import java.io.*;

class HashMap$EntryIterator extends HashMap$HashIterator {
    
    /*synthetic*/ HashMap$EntryIterator(HashMap x0, java.util.HashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final HashMap this$0;
    
    private HashMap$EntryIterator(/*synthetic*/ final HashMap this$0) {
        super(this.this$0 =this$0);
    }
    
    public Map$Entry next() {
        return nextEntry();
    }
    
    /*synthetic public Object next() {
        return this.next();
    } */
}
