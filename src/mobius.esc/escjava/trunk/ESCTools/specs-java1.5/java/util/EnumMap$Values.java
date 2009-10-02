package java.util;

class EnumMap$Values extends AbstractCollection {
    
    /*synthetic*/ EnumMap$Values(EnumMap x0, java.util.EnumMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final EnumMap this$0;
    
    private EnumMap$Values(/*synthetic*/ final EnumMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new EnumMap$ValueIterator(this$0, null);
    }
    
    public int size() {
        return EnumMap.access$200(this$0);
    }
    
    public boolean contains(Object o) {
        return this$0.containsValue(o);
    }
    
    public boolean remove(Object o) {
        o = EnumMap.access$500(this$0, o);
        for (int i = 0; i < EnumMap.access$600(this$0).length; i++) {
            if (o.equals(EnumMap.access$600(this$0)[i])) {
                EnumMap.access$600(this$0)[i] = null;
                EnumMap.access$210(this$0);
                return true;
            }
        }
        return false;
    }
    
    public void clear() {
        this$0.clear();
    }
}
