package java.util;

class AbstractList$Itr implements Iterator {
    
    /*synthetic*/ AbstractList$Itr(AbstractList x0, java.util.AbstractList$1 x1) {
        this(x0);
    }
    /*synthetic*/ final AbstractList this$0;
    
    private AbstractList$Itr(/*synthetic*/ final AbstractList this$0) {
        this.this$0 = this$0;
        
    }
    int cursor = 0;
    int lastRet = -1;
    int expectedModCount = this$0.modCount;
    
    public boolean hasNext() {
        return cursor != this$0.size();
    }
    
    public Object next() {
        checkForComodification();
        try {
            Object next = this$0.get(cursor);
            lastRet = cursor++;
            return next;
        } catch (IndexOutOfBoundsException e) {
            checkForComodification();
            throw new NoSuchElementException();
        }
    }
    
    public void remove() {
        if (lastRet == -1) throw new IllegalStateException();
        checkForComodification();
        try {
            this$0.remove(lastRet);
            if (lastRet < cursor) cursor--;
            lastRet = -1;
            expectedModCount = this$0.modCount;
        } catch (IndexOutOfBoundsException e) {
            throw new ConcurrentModificationException();
        }
    }
    
    final void checkForComodification() {
        if (this$0.modCount != expectedModCount) throw new ConcurrentModificationException();
    }
}
