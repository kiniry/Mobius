package java.util;

class Collections$1 implements Enumeration {
    /*synthetic*/ final Collection val$c;
    
    Collections$1(/*synthetic*/ final Collection val$c) {
        this.val$c = val$c;
        
    }
    Iterator i = val$c.iterator();
    
    public boolean hasMoreElements() {
        return i.hasNext();
    }
    
    public Object nextElement() {
        return i.next();
    }
}
