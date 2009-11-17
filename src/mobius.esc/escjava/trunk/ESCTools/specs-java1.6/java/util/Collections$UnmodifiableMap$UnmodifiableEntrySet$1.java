package java.util;

class Collections$UnmodifiableMap$UnmodifiableEntrySet$1 implements Iterator {
    /*synthetic*/ final Collections$UnmodifiableMap$UnmodifiableEntrySet this$0;
    
    Collections$UnmodifiableMap$UnmodifiableEntrySet$1(/*synthetic*/ final Collections$UnmodifiableMap$UnmodifiableEntrySet this$0) {
        this.this$0 = this$0;
        
    }
    Iterator i = this$0.c.iterator();
    
    public boolean hasNext() {
        return i.hasNext();
    }
    
    public Map$Entry next() {
        return new Collections$UnmodifiableMap$UnmodifiableEntrySet$UnmodifiableEntry((Map$Entry)i.next());
    }
    
    public void remove() {
        throw new UnsupportedOperationException();
    }
    
    /*synthetic public Object next() {
        return this.next();
    } */
}
