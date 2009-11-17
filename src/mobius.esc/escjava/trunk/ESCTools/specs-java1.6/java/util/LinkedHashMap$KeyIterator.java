package java.util;

import java.io.*;

class LinkedHashMap$KeyIterator extends LinkedHashMap$LinkedHashIterator {
    
    /*synthetic*/ LinkedHashMap$KeyIterator(LinkedHashMap x0, java.util.LinkedHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final LinkedHashMap this$0;
    
    private LinkedHashMap$KeyIterator(/*synthetic*/ final LinkedHashMap this$0) {
        super(this.this$0 = this$0, null);
    }
    
    public Object next() {
        return nextEntry().getKey();
    }
}
