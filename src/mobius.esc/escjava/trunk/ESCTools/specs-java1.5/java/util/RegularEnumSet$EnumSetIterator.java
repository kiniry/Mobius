package java.util;

class RegularEnumSet$EnumSetIterator implements Iterator {
    /*synthetic*/ final RegularEnumSet this$0;
    long unseen;
    long lastReturned = 0;
    
    RegularEnumSet$EnumSetIterator(/*synthetic*/ final RegularEnumSet this$0) {
        this.this$0 = this$0;
        
        unseen = RegularEnumSet.access$000(this$0);
    }
    
    public boolean hasNext() {
        return unseen != 0;
    }
    
    public Enum next() {
        if (unseen == 0) throw new NoSuchElementException();
        lastReturned = unseen & -unseen;
        unseen -= lastReturned;
        return (Enum)this$0.universe[Long.numberOfTrailingZeros(lastReturned)];
    }
    
    public void remove() {
        if (lastReturned == 0) throw new IllegalStateException();
        RegularEnumSet.access$022(this$0, lastReturned);
        lastReturned = 0;
    }
    
    /*synthetic public Object next() {
        return this.next();
    } */
}
