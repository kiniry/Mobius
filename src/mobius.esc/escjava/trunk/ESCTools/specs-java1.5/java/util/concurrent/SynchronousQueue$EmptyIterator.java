package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

class SynchronousQueue$EmptyIterator implements Iterator {
    
    SynchronousQueue$EmptyIterator() {
        
    }
    
    public boolean hasNext() {
        return false;
    }
    
    public Object next() {
        throw new NoSuchElementException();
    }
    
    public void remove() {
        throw new IllegalStateException();
    }
}
