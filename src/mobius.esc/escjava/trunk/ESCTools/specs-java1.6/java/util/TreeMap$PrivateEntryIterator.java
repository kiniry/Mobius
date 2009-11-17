package java.util;

abstract class TreeMap$PrivateEntryIterator implements Iterator {
    /*synthetic*/ final TreeMap this$0;
    private int expectedModCount = TreeMap.access$1600(this$0);
    private TreeMap$Entry lastReturned = null;
    TreeMap$Entry next;
    
    TreeMap$PrivateEntryIterator(/*synthetic*/ final TreeMap this$0) {
        this.this$0 = this$0;
        
        next = TreeMap.access$300(this$0);
    }
    
    TreeMap$PrivateEntryIterator(/*synthetic*/ final TreeMap this$0, TreeMap$Entry first) {
        this.this$0 = this$0;
        
        next = first;
    }
    
    public boolean hasNext() {
        return next != null;
    }
    
    final TreeMap$Entry nextEntry() {
        if (next == null) throw new NoSuchElementException();
        if (TreeMap.access$1600(this$0) != expectedModCount) throw new ConcurrentModificationException();
        lastReturned = next;
        next = TreeMap.access$400(this$0, next);
        return lastReturned;
    }
    
    public void remove() {
        if (lastReturned == null) throw new IllegalStateException();
        if (TreeMap.access$1600(this$0) != expectedModCount) throw new ConcurrentModificationException();
        if (lastReturned.left != null && lastReturned.right != null) next = lastReturned;
        TreeMap.access$600(this$0, lastReturned);
        expectedModCount++;
        lastReturned = null;
    }
}
