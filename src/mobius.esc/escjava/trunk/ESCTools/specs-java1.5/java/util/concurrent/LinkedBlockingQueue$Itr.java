package java.util.concurrent;

import java.util.concurrent.atomic.*;
import java.util.concurrent.locks.*;
import java.util.*;

class LinkedBlockingQueue$Itr implements Iterator {
    /*synthetic*/ final LinkedBlockingQueue this$0;
    private LinkedBlockingQueue$Node current;
    private LinkedBlockingQueue$Node lastRet;
    private Object currentElement;
    
    LinkedBlockingQueue$Itr(/*synthetic*/ final LinkedBlockingQueue this$0) {
        this.this$0 = this$0;
        
        final ReentrantLock putLock = LinkedBlockingQueue.access$000(this$0);
        final ReentrantLock takeLock = LinkedBlockingQueue.access$100(this$0);
        putLock.lock();
        takeLock.lock();
        try {
            current = LinkedBlockingQueue.access$200(this$0).next;
            if (current != null) currentElement = current.item;
        } finally {
            takeLock.unlock();
            putLock.unlock();
        }
    }
    
    public boolean hasNext() {
        return current != null;
    }
    
    public Object next() {
        final ReentrantLock putLock = LinkedBlockingQueue.access$000(this$0);
        final ReentrantLock takeLock = LinkedBlockingQueue.access$100(this$0);
        putLock.lock();
        takeLock.lock();
        try {
            if (current == null) throw new NoSuchElementException();
            Object x = currentElement;
            lastRet = current;
            current = current.next;
            if (current != null) currentElement = current.item;
            return x;
        } finally {
            takeLock.unlock();
            putLock.unlock();
        }
    }
    
    public void remove() {
        if (lastRet == null) throw new IllegalStateException();
        final ReentrantLock putLock = LinkedBlockingQueue.access$000(this$0);
        final ReentrantLock takeLock = LinkedBlockingQueue.access$100(this$0);
        putLock.lock();
        takeLock.lock();
        try {
            LinkedBlockingQueue$Node node = lastRet;
            lastRet = null;
            LinkedBlockingQueue$Node trail = LinkedBlockingQueue.access$200(this$0);
            LinkedBlockingQueue$Node p = LinkedBlockingQueue.access$200(this$0).next;
            while (p != null && p != node) {
                trail = p;
                p = p.next;
            }
            if (p == node) {
                p.item = null;
                trail.next = p.next;
                if (LinkedBlockingQueue.access$300(this$0) == p) LinkedBlockingQueue.access$302(this$0, trail);
                int c = LinkedBlockingQueue.access$400(this$0).getAndDecrement();
                if (c == LinkedBlockingQueue.access$500(this$0)) LinkedBlockingQueue.access$600(this$0).signalAll();
            }
        } finally {
            takeLock.unlock();
            putLock.unlock();
        }
    }
}
