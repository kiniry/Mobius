package java.util;

import java.util.Map.Entry;

class AbstractMap$1$1 implements Iterator {
    /*synthetic*/ final AbstractMap$1 this$1;
    
    AbstractMap$1$1(/*synthetic*/ final AbstractMap$1 this$1) {
        this.this$1 = this$1;
        
    }
    private Iterator i = this$1.this$0.entrySet().iterator();
    
    public boolean hasNext() {
        return i.hasNext();
    }
    
    public Object next() {
        return ((Map$Entry)i.next()).getKey();
    }
    
    public void remove() {
        i.remove();
    }
}
