package java.util;

class TreeMap$SubMapEntryIterator extends TreeMap$PrivateEntryIterator {
    /*synthetic*/ final TreeMap this$0;
    private final Object firstExcludedKey;
    
    TreeMap$SubMapEntryIterator(/*synthetic*/ final TreeMap this$0, TreeMap$Entry first, TreeMap$Entry firstExcluded) {
        super(this.this$0 = this$0, first);
        firstExcludedKey = (firstExcluded == null ? null : firstExcluded.key);
    }
    
    public boolean hasNext() {
        return next != null && next.key != firstExcludedKey;
    }
    
    public Map$Entry next() {
        if (next == null || next.key == firstExcludedKey) throw new NoSuchElementException();
        return nextEntry();
    }
    
    /*synthetic public Object next() {
        return this.next();
    } */
}
