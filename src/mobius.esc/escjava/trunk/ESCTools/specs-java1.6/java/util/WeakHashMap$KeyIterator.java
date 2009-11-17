package java.util;

class WeakHashMap$KeyIterator extends WeakHashMap$HashIterator {
    
    /*synthetic*/ WeakHashMap$KeyIterator(WeakHashMap x0, java.util.WeakHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final WeakHashMap this$0;
    
    private WeakHashMap$KeyIterator(/*synthetic*/ final WeakHashMap this$0) {
        super( this.this$0 = this$0);
    }
    
    public Object next() {
        return nextEntry().getKey();
    }
}
