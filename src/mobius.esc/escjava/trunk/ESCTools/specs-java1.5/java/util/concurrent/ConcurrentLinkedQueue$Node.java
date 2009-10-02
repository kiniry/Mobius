package java.util.concurrent;

import java.util.*;
import java.util.concurrent.atomic.*;

class ConcurrentLinkedQueue$Node {
    private volatile Object item;
    private volatile ConcurrentLinkedQueue$Node next;
    private static final AtomicReferenceFieldUpdater nextUpdater = AtomicReferenceFieldUpdater.newUpdater(ConcurrentLinkedQueue.Node.class, ConcurrentLinkedQueue.Node.class, "next");
    private static final AtomicReferenceFieldUpdater itemUpdater = AtomicReferenceFieldUpdater.newUpdater(ConcurrentLinkedQueue.Node.class, Object.class, "item");
    
    ConcurrentLinkedQueue$Node(Object x) {
        
        item = x;
    }
    
    ConcurrentLinkedQueue$Node(Object x, ConcurrentLinkedQueue$Node n) {
        
        item = x;
        next = n;
    }
    
    Object getItem() {
        return item;
    }
    
    boolean casItem(Object cmp, Object val) {
        return itemUpdater.compareAndSet(this, cmp, val);
    }
    
    void setItem(Object val) {
        itemUpdater.set(this, val);
    }
    
    ConcurrentLinkedQueue$Node getNext() {
        return next;
    }
    
    boolean casNext(ConcurrentLinkedQueue$Node cmp, ConcurrentLinkedQueue$Node val) {
        return nextUpdater.compareAndSet(this, cmp, val);
    }
    
    void setNext(ConcurrentLinkedQueue$Node val) {
        nextUpdater.set(this, val);
    }
}
