package java.util;

class Collections$SingletonSet$1 implements Iterator {
    /*synthetic*/ final Collections$SingletonSet this$0;
    
    Collections$SingletonSet$1(/*synthetic*/ final Collections$SingletonSet this$0) {
        this.this$0 = this$0;
        
    }
    private boolean hasNext = true;
    
    public boolean hasNext() {
        return hasNext;
    }
    
    public Object next() {
        if (hasNext) {
            hasNext = false;
            return Collections.SingletonSet.access$400(this$0);
        }
        throw new NoSuchElementException();
    }
    
    public void remove() {
        throw new UnsupportedOperationException();
    }
}
