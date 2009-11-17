package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

class DelayQueue$Itr implements Iterator {
    /*synthetic*/ final DelayQueue this$0;
    private final Iterator iter;
    
    DelayQueue$Itr(/*synthetic*/ final DelayQueue this$0, Iterator i) {
        this.this$0 = this$0;
        
        iter = i;
    }
    
    public boolean hasNext() {
        return iter.hasNext();
    }
    
    public Object next() {
        final ReentrantLock lock = DelayQueue.access$000(this$0);
        lock.lock();
        try {
            return iter.next();
        } finally {
            lock.unlock();
        }
    }
    
    public void remove() {
        final ReentrantLock lock = DelayQueue.access$000(this$0);
        lock.lock();
        try {
            iter.remove();
        } finally {
            lock.unlock();
        }
    }
}
