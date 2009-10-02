package java.util;

class AbstractList$ListItr extends AbstractList$Itr implements ListIterator {
    /*synthetic*/ final AbstractList this$0;
    
    AbstractList$ListItr(/*synthetic*/ final AbstractList this$0, int index) {
        super(this.this$0 = this$0, null);
        cursor = index;
    }
    
    public boolean hasPrevious() {
        return cursor != 0;
    }
    
    public Object previous() {
        checkForComodification();
        try {
            int i = cursor - 1;
            Object previous = this$0.get(i);
            lastRet = cursor = i;
            return previous;
        } catch (IndexOutOfBoundsException e) {
            checkForComodification();
            throw new NoSuchElementException();
        }
    }
    
    public int nextIndex() {
        return cursor;
    }
    
    public int previousIndex() {
        return cursor - 1;
    }
    
    public void set(Object o) {
        if (lastRet == -1) throw new IllegalStateException();
        checkForComodification();
        try {
            this$0.set(lastRet, o);
            expectedModCount = this$0.modCount;
        } catch (IndexOutOfBoundsException e) {
            throw new ConcurrentModificationException();
        }
    }
    
    public void add(Object o) {
        checkForComodification();
        try {
            this$0.add(cursor++, o);
            lastRet = -1;
            expectedModCount = this$0.modCount;
        } catch (IndexOutOfBoundsException e) {
            throw new ConcurrentModificationException();
        }
    }
}
