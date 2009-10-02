package java.util;

class JumboEnumSet$EnumSetIterator implements Iterator {
    /*synthetic*/ final JumboEnumSet this$0;
    long unseen;
    int unseenIndex = 0;
    long lastReturned = 0;
    int lastReturnedIndex = 0;
    
    JumboEnumSet$EnumSetIterator(/*synthetic*/ final JumboEnumSet this$0) {
        this.this$0 = this$0;
        
        unseen = JumboEnumSet.access$000(this$0)[0];
    }
    
    public boolean hasNext() {
        while (unseen == 0 && unseenIndex < JumboEnumSet.access$000(this$0).length - 1) unseen = JumboEnumSet.access$000(this$0)[++unseenIndex];
        return unseen != 0;
    }
    
    public Enum next() {
        if (!hasNext()) throw new NoSuchElementException();
        lastReturned = unseen & -unseen;
        lastReturnedIndex = unseenIndex;
        unseen -= lastReturned;
        return (Enum)this$0.universe[(lastReturnedIndex << 6) + Long.numberOfTrailingZeros(lastReturned)];
    }
    
    public void remove() {
        if (lastReturned == 0) throw new IllegalStateException();
        JumboEnumSet.access$000(this$0)[lastReturnedIndex] -= lastReturned;
        JumboEnumSet.access$110(this$0);
        lastReturned = 0;
    }
    
    /*synthetic public Object next() {
        return this.next();
    } */
}
