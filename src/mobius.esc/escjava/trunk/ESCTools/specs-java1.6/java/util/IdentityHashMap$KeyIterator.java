package java.util;

import java.io.*;

class IdentityHashMap$KeyIterator extends IdentityHashMap$IdentityHashMapIterator {
    
    /*synthetic*/ IdentityHashMap$KeyIterator(IdentityHashMap x0, java.util.IdentityHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final IdentityHashMap this$0;
    
    private IdentityHashMap$KeyIterator(/*synthetic*/ final IdentityHashMap this$0) {
        super(this$0, null);

    	this.this$0 = this$0;
    }
    
    public Object next() {
        return (Object)IdentityHashMap.access$600(traversalTable[nextIndex()]);
    }
}
