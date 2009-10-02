package java.util.concurrent;

import java.util.*;
import java.util.concurrent.atomic.*;

class ConcurrentLinkedQueue$Itr implements Iterator {
    /*synthetic*/ final ConcurrentLinkedQueue this$0;
    private ConcurrentLinkedQueue$Node nextNode;
    private Object nextItem;
    private ConcurrentLinkedQueue$Node lastRet;
    
    ConcurrentLinkedQueue$Itr(/*synthetic*/ final ConcurrentLinkedQueue this$0) {
        this.this$0 = this$0;
        
        advance();
    }
    
    private Object advance() {
        lastRet = nextNode;
        Object x = nextItem;
        ConcurrentLinkedQueue$Node p = (nextNode == null) ? this$0.first() : nextNode.getNext();
        for (; ; ) {
            if (p == null) {
                nextNode = null;
                nextItem = null;
                return x;
            }
            Object item = p.getItem();
            if (item != null) {
                nextNode = p;
                nextItem = item;
                return x;
            } else p = p.getNext();
        }
    }
    
    public boolean hasNext() {
        return nextNode != null;
    }
    
    public Object next() {
        if (nextNode == null) throw new NoSuchElementException();
        return advance();
    }
    
    public void remove() {
        ConcurrentLinkedQueue$Node l = lastRet;
        if (l == null) throw new IllegalStateException();
        l.setItem(null);
        lastRet = null;
    }
}
