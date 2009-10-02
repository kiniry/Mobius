package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

final class ConcurrentHashMap$ValueIterator extends ConcurrentHashMap$HashIterator implements Iterator, Enumeration {
    /*synthetic*/ final ConcurrentHashMap this$0;
    
    ConcurrentHashMap$ValueIterator(/*synthetic*/ final ConcurrentHashMap this$0) {
        super(this$0);
        this.this$0 = this$0;

    }
    
    public Object next() {
        return super.nextEntry().value;
    }
    
    public Object nextElement() {
        return super.nextEntry().value;
    }
}
