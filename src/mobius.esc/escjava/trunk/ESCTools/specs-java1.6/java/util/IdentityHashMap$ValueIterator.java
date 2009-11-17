package java.util;

import java.io.*;

class IdentityHashMap$ValueIterator extends IdentityHashMap$IdentityHashMapIterator {
    
    /*synthetic*/ IdentityHashMap$ValueIterator(IdentityHashMap x0, java.util.IdentityHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final IdentityHashMap this$0;
    
    private IdentityHashMap$ValueIterator(/*synthetic*/ final IdentityHashMap this$0) {
        super(this.this$0 = this$0, null);
    }
    
    public Object next() {
        return (Object)traversalTable[nextIndex() + 1];
    }
}
