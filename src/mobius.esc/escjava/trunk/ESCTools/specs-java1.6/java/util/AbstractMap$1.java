package java.util;

class AbstractMap$1 extends AbstractSet {
    /*synthetic*/ final AbstractMap this$0;
    
    AbstractMap$1(/*synthetic*/ final AbstractMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new AbstractMap$1$1(this);
    }
    
    public int size() {
        return this$0.size();
    }
    
    public boolean contains(Object k) {
        return this$0.containsKey(k);
    }
}
