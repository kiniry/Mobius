package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

class PriorityBlockingQueue$Itr implements Iterator {
    /*synthetic*/ final PriorityBlockingQueue this$0;
    private final Iterator iter;
    
    PriorityBlockingQueue$Itr(/*synthetic*/ final PriorityBlockingQueue this$0, Iterator i) {
        this.this$0 = this$0;
        
        iter = i;
    }
    
    public boolean hasNext() {
        return iter.hasNext();
    }
    
    public Object next() {
        ReentrantLock lock = PriorityBlockingQueue.access$000(this$0);
        lock.lock();
        try {
            return iter.next();
        } finally {
            lock.unlock();
        }
    }
    
    public void remove() {
        ReentrantLock lock = PriorityBlockingQueue.access$000(this$0);
        lock.lock();
        try {
            iter.remove();
        } finally {
            lock.unlock();
        }
    }
}
