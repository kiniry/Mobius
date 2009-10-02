package java.util;

class Collections$UnmodifiableList$1 implements ListIterator {
    /*synthetic*/ final Collections$UnmodifiableList this$0;
    /*synthetic*/ final int val$index;
    
    Collections$UnmodifiableList$1(/*synthetic*/ final Collections$UnmodifiableList this$0, /*synthetic*/ final int val$index) {
        this.this$0 = this$0;
        this.val$index = val$index;
        
    }
    ListIterator i = this$0.list.listIterator(val$index);
    
    public boolean hasNext() {
        return i.hasNext();
    }
    
    public Object next() {
        return i.next();
    }
    
    public boolean hasPrevious() {
        return i.hasPrevious();
    }
    
    public Object previous() {
        return i.previous();
    }
    
    public int nextIndex() {
        return i.nextIndex();
    }
    
    public int previousIndex() {
        return i.previousIndex();
    }
    
    public void remove() {
        throw new UnsupportedOperationException();
    }
    
    public void set(Object o) {
        throw new UnsupportedOperationException();
    }
    
    public void add(Object o) {
        throw new UnsupportedOperationException();
    }
}
