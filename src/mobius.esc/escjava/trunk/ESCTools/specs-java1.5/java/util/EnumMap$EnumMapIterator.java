package java.util;

abstract class EnumMap$EnumMapIterator implements Iterator {
    
    /*synthetic*/ EnumMap$EnumMapIterator(EnumMap x0, java.util.EnumMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final EnumMap this$0;
    
    private EnumMap$EnumMapIterator(/*synthetic*/ final EnumMap this$0) {
        this.this$0 = this$0;
        
    }
    int index = 0;
    int lastReturnedIndex = -1;
    
    public boolean hasNext() {
        while (index < EnumMap.access$600(this$0).length && EnumMap.access$600(this$0)[index] == null) index++;
        return index != EnumMap.access$600(this$0).length;
    }
    
    public void remove() {
        checkLastReturnedIndex();
        if (EnumMap.access$600(this$0)[lastReturnedIndex] != null) {
            EnumMap.access$600(this$0)[lastReturnedIndex] = null;
            EnumMap.access$210(this$0);
        }
        lastReturnedIndex = -1;
    }
    
    private void checkLastReturnedIndex() {
        if (lastReturnedIndex < 0) throw new IllegalStateException();
    }
}
