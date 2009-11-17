package java.util;

class EnumMap$ValueIterator extends EnumMap$EnumMapIterator {
    
    /*synthetic*/ EnumMap$ValueIterator(EnumMap x0, java.util.EnumMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final EnumMap this$0;
    
    private EnumMap$ValueIterator(/*synthetic*/ final EnumMap this$0) {
        super(this$0, null);

    	this.this$0 = this$0;
    }
    
    public Object next() {
        if (!hasNext()) throw new NoSuchElementException();
        lastReturnedIndex = index++;
        return EnumMap.access$1200(this$0, EnumMap.access$600(this$0)[lastReturnedIndex]);
    }
}
