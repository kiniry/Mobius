package java.util;

class Collections$CheckedCollection$1 implements Iterator {
    /*synthetic*/ final Collections$CheckedCollection this$0;
    
    Collections$CheckedCollection$1(/*synthetic*/ final Collections$CheckedCollection this$0) {
        this.this$0 = this$0;
        
    }
    private final Iterator it = this$0.c.iterator();
    
    public boolean hasNext() {
        return it.hasNext();
    }
    
    public Object next() {
        return it.next();
    }
    
    public void remove() {
        it.remove();
    }
}
