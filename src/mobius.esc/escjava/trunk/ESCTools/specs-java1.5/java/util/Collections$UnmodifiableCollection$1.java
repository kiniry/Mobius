package java.util;

class Collections$UnmodifiableCollection$1 implements Iterator {
    /*synthetic*/ final Collections$UnmodifiableCollection this$0;
    
    Collections$UnmodifiableCollection$1(/*synthetic*/ final Collections$UnmodifiableCollection this$0) {
        this.this$0 = this$0;
        
    }
    Iterator i = this$0.c.iterator();
    
    public boolean hasNext() {
        return i.hasNext();
    }
    
    public Object next() {
        return i.next();
    }
    
    public void remove() {
        throw new UnsupportedOperationException();
    }
}
