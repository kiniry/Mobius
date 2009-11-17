package java.util;

class Collections$EmptySet$1 implements Iterator {
    /*synthetic*/ final Collections$EmptySet this$0;
    
    Collections$EmptySet$1(/*synthetic*/ final Collections$EmptySet this$0) {
        this.this$0 = this$0;
        
    }
    
    public boolean hasNext() {
        return false;
    }
    
    public Object next() {
        throw new NoSuchElementException();
    }
    
    public void remove() {
        throw new UnsupportedOperationException();
    }
}
