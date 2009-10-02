package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

class ArrayBlockingQueue$Itr implements Iterator {
    /*synthetic*/ final ArrayBlockingQueue this$0;
    private int nextIndex;
    private Object nextItem;
    private int lastRet;
    
    ArrayBlockingQueue$Itr(/*synthetic*/ final ArrayBlockingQueue this$0) {
        this.this$0 = this$0;
        
        lastRet = -1;
        if (ArrayBlockingQueue.access$000(this$0) == 0) nextIndex = -1; else {
            nextIndex = ArrayBlockingQueue.access$100(this$0);
            nextItem = ArrayBlockingQueue.access$200(this$0)[ArrayBlockingQueue.access$100(this$0)];
        }
    }
    
    public boolean hasNext() {
        return nextIndex >= 0;
    }
    
    private void checkNext() {
        if (nextIndex == ArrayBlockingQueue.access$300(this$0)) {
            nextIndex = -1;
            nextItem = null;
        } else {
            nextItem = ArrayBlockingQueue.access$200(this$0)[nextIndex];
            if (nextItem == null) nextIndex = -1;
        }
    }
    
    public Object next() {
        final ReentrantLock lock = ArrayBlockingQueue.access$400(this$0);
        lock.lock();
        try {
            if (nextIndex < 0) throw new NoSuchElementException();
            lastRet = nextIndex;
            Object x = nextItem;
            nextIndex = this$0.inc(nextIndex);
            checkNext();
            return x;
        } finally {
            lock.unlock();
        }
    }
    
    public void remove() {
        final ReentrantLock lock = ArrayBlockingQueue.access$400(this$0);
        lock.lock();
        try {
            int i = lastRet;
            if (i == -1) throw new IllegalStateException();
            lastRet = -1;
            int ti = ArrayBlockingQueue.access$100(this$0);
            this$0.removeAt(i);
            nextIndex = (i == ti) ? ArrayBlockingQueue.access$100(this$0) : i;
            checkNext();
        } finally {
            lock.unlock();
        }
    }
}
