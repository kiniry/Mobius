package java.util;

class Collections$CheckedMap$CheckedEntrySet$1 implements Iterator {
    /*synthetic*/ final Collections$CheckedMap$CheckedEntrySet this$0;
    
    Collections$CheckedMap$CheckedEntrySet$1(/*synthetic*/ final Collections$CheckedMap$CheckedEntrySet this$0) {
        this.this$0 = this$0;
        
    }
    Iterator i = this$0.s.iterator();
    
    public boolean hasNext() {
        return i.hasNext();
    }
    
    public void remove() {
        i.remove();
    }
    
    public Map$Entry next() {
        return new Collections$CheckedMap$CheckedEntrySet$CheckedEntry((Map$Entry)i.next(), this$0.valueType);
    }
    
    /*synthetic public Object next() {
        return this.next();
    } */
}
