package java.util;

class TreeMap$KeyIterator extends TreeMap$PrivateEntryIterator {
    
    /*synthetic*/ TreeMap$KeyIterator(TreeMap x0, java.util.TreeMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final TreeMap this$0;
    
    private TreeMap$KeyIterator(/*synthetic*/ final TreeMap this$0) {
        super( this.this$0 = this$0);
    }
    
    public Object next() {
        return nextEntry().key;
    }
}
