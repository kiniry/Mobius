package java.util;

import java.io.*;

class Hashtable$EmptyIterator implements Iterator {
    
    Hashtable$EmptyIterator() {
        
    }
    
    public boolean hasNext() {
        return false;
    }
    
    public Object next() {
        throw new NoSuchElementException("Hashtable Iterator");
    }
    
    public void remove() {
        throw new IllegalStateException("Hashtable Iterator");
    }
}
