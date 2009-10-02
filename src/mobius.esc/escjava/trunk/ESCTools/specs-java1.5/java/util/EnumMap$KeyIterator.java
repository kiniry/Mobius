package java.util;

class EnumMap$KeyIterator extends EnumMap$EnumMapIterator {
    
    /*synthetic*/ EnumMap$KeyIterator(EnumMap x0, java.util.EnumMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final EnumMap this$0;
    
    private EnumMap$KeyIterator(/*synthetic*/ final EnumMap this$0) {
        super(this.this$0 = this$0, null);
    }
    
    public Enum next() {
        if (!hasNext()) throw new NoSuchElementException();
        lastReturnedIndex = index++;
        return EnumMap.access$1100(this$0)[lastReturnedIndex];
    }
    
    /*synthetic public Object next() {
        return this.next();
    } */
}
