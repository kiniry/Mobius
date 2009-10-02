package java.util;

import java.io.*;

class Hashtable$EmptyEnumerator implements Enumeration {
    
    Hashtable$EmptyEnumerator() {
        
    }
    
    public boolean hasMoreElements() {
        return false;
    }
    
    public Object nextElement() {
        throw new NoSuchElementException("Hashtable Enumerator");
    }
}
