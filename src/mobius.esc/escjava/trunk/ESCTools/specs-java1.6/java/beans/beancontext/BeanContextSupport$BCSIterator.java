package java.beans.beancontext;

import java.util.Iterator;

public final class BeanContextSupport$BCSIterator implements Iterator {
    
    BeanContextSupport$BCSIterator(Iterator i) {
        
        src = i;
    }
    
    public boolean hasNext() {
        return src.hasNext();
    }
    
    public Object next() {
        return src.next();
    }
    
    public void remove() {
    }
    private Iterator src;
}
