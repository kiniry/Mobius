package java.util;

class TreeMap$ValueIterator extends TreeMap$PrivateEntryIterator {
    
    /*synthetic*/ TreeMap$ValueIterator(TreeMap x0, java.util.TreeMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final TreeMap this$0;
    
    private TreeMap$ValueIterator(/*synthetic*/ final TreeMap this$0) {
        super(this.this$0 = this$0);
    }
    
    public Object next() {
        return nextEntry().value;
    }
}
