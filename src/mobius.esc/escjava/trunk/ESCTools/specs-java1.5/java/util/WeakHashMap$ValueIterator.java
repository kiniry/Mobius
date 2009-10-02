package java.util;

class WeakHashMap$ValueIterator extends WeakHashMap$HashIterator {
    
    /*synthetic*/ WeakHashMap$ValueIterator(WeakHashMap x0, java.util.WeakHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final WeakHashMap this$0;
    
    private WeakHashMap$ValueIterator(/*synthetic*/ final WeakHashMap this$0) {
        super(this.this$0 = this$0);
    }
    
    public Object next() {
        return WeakHashMap.Entry.access$200(nextEntry());
    }
}
