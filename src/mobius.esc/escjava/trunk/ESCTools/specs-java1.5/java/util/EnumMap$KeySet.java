package java.util;

class EnumMap$KeySet extends AbstractSet {
    
    /*synthetic*/ EnumMap$KeySet(EnumMap x0, java.util.EnumMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final EnumMap this$0;
    
    private EnumMap$KeySet(/*synthetic*/ final EnumMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new EnumMap$KeyIterator(this$0, null);
    }
    
    public int size() {
        return EnumMap.access$200(this$0);
    }
    
    public boolean contains(Object o) {
        return this$0.containsKey(o);
    }
    
    public boolean remove(Object o) {
        int oldSize = EnumMap.access$200(this$0);
        this$0.remove(o);
        return EnumMap.access$200(this$0) != oldSize;
    }
    
    public void clear() {
        this$0.clear();
    }
}
