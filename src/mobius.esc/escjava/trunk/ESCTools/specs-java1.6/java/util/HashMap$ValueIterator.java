package java.util;

import java.io.*;

class HashMap$ValueIterator extends HashMap$HashIterator {
    
    /*synthetic*/ HashMap$ValueIterator(HashMap x0, java.util.HashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final HashMap this$0;
    
    private HashMap$ValueIterator(/*synthetic*/ final HashMap this$0) {
        super( this.this$0 = this$0);
    }
    
    public Object next() {
        return nextEntry().value;
    }
}
