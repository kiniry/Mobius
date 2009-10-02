package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

final class ConcurrentHashMap$KeyIterator extends ConcurrentHashMap$HashIterator implements Iterator, Enumeration {
    /*synthetic*/ final ConcurrentHashMap this$0;
    
    ConcurrentHashMap$KeyIterator(/*synthetic*/ final ConcurrentHashMap this$0) {
        super(this.this$0 = this$0);
    }
    
    public Object next() {
        return super.nextEntry().key;
    }
    
    public Object nextElement() {
        return super.nextEntry().key;
    }
}
