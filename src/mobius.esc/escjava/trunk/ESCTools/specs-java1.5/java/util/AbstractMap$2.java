package java.util;

class AbstractMap$2 extends AbstractCollection {
    /*synthetic*/ final AbstractMap this$0;
    
    AbstractMap$2(/*synthetic*/ final AbstractMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new AbstractMap$2$1(this);
    }
    
    public int size() {
        return this$0.size();
    }
    
    public boolean contains(Object v) {
        return this$0.containsValue(v);
    }
}
