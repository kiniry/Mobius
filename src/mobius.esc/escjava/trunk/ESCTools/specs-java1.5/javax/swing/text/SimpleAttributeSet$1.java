package javax.swing.text;

import java.util.Enumeration;
import java.util.NoSuchElementException;

class SimpleAttributeSet$1 implements Enumeration {
    
    SimpleAttributeSet$1() {
        
    }
    
    public boolean hasMoreElements() {
        return false;
    }
    
    public Object nextElement() {
        throw new NoSuchElementException("No more elements");
    }
}
