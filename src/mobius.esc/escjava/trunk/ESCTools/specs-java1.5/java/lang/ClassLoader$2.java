package java.lang;

import java.util.Enumeration;
import sun.misc.Resource;

class ClassLoader$2 implements Enumeration {
    /*synthetic*/ final Enumeration val$e;
    
    ClassLoader$2(/*synthetic*/ final Enumeration val$e) {
        this.val$e = val$e;
        
    }
    
    public Object nextElement() {
        return ((Resource)(Resource)val$e.nextElement()).getURL();
    }
    
    public boolean hasMoreElements() {
        return val$e.hasMoreElements();
    }
}
