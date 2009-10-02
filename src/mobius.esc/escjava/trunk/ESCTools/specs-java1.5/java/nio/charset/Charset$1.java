package java.nio.charset;

import java.nio.charset.spi.CharsetProvider;
import java.util.Iterator;
import java.util.NoSuchElementException;
import sun.misc.Service;
import sun.misc.ServiceConfigurationError;

class Charset$1 implements Iterator {
    
    Charset$1() {
        
    }
    Class c = CharsetProvider.class;
    ClassLoader cl = ClassLoader.getSystemClassLoader();
    Iterator i = Service.providers(c, cl);
    Object next = null;
    
    private boolean getNext() {
        while (next == null) {
            try {
                if (!i.hasNext()) return false;
                next = i.next();
            } catch (ServiceConfigurationError sce) {
                if (sce.getCause() instanceof SecurityException) {
                    continue;
                }
                throw sce;
            }
        }
        return true;
    }
    
    public boolean hasNext() {
        return getNext();
    }
    
    public Object next() {
        if (!getNext()) throw new NoSuchElementException();
        Object n = next;
        next = null;
        return n;
    }
    
    public void remove() {
        throw new UnsupportedOperationException();
    }
}
