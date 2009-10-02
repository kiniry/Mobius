package java.util;

class LinkedList$ListItr implements ListIterator {
    /*synthetic*/ final LinkedList this$0;
    private LinkedList$Entry lastReturned = LinkedList.access$000(this$0);
    private LinkedList$Entry next;
    private int nextIndex;
    private int expectedModCount = this$0.modCount;
    
    LinkedList$ListItr(/*synthetic*/ final LinkedList this$0, int index) {
        this.this$0 = this$0;
        
        if (index < 0 || index > LinkedList.access$100(this$0)) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + LinkedList.access$100(this$0));
        if (index < (LinkedList.access$100(this$0) >> 1)) {
            next = LinkedList.access$000(this$0).next;
            for (nextIndex = 0; nextIndex < index; nextIndex++) next = next.next;
        } else {
            next = LinkedList.access$000(this$0);
            for (nextIndex = LinkedList.access$100(this$0); nextIndex > index; nextIndex--) next = next.previous;
        }
    }
    
    public boolean hasNext() {
        return nextIndex != LinkedList.access$100(this$0);
    }
    
    public Object next() {
        checkForComodification();
        if (nextIndex == LinkedList.access$100(this$0)) throw new NoSuchElementException();
        lastReturned = next;
        next = next.next;
        nextIndex++;
        return lastReturned.element;
    }
    
    public boolean hasPrevious() {
        return nextIndex != 0;
    }
    
    public Object previous() {
        if (nextIndex == 0) throw new NoSuchElementException();
        lastReturned = next = next.previous;
        nextIndex--;
        checkForComodification();
        return lastReturned.element;
    }
    
    public int nextIndex() {
        return nextIndex;
    }
    
    public int previousIndex() {
        return nextIndex - 1;
    }
    
    public void remove() {
        checkForComodification();
        LinkedList$Entry lastNext = lastReturned.next;
        try {
            LinkedList.access$200(this$0, lastReturned);
        } catch (NoSuchElementException e) {
            throw new IllegalStateException();
        }
        if (next == lastReturned) next = lastNext; else nextIndex--;
        lastReturned = LinkedList.access$000(this$0);
        expectedModCount++;
    }
    
    public void set(Object o) {
        if (lastReturned == LinkedList.access$000(this$0)) throw new IllegalStateException();
        checkForComodification();
        lastReturned.element = o;
    }
    
    public void add(Object o) {
        checkForComodification();
        lastReturned = LinkedList.access$000(this$0);
        LinkedList.access$300(this$0, o, next);
        nextIndex++;
        expectedModCount++;
    }
    
    final void checkForComodification() {
        if (this$0.modCount != expectedModCount) throw new ConcurrentModificationException();
    }
}
