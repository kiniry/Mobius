package java.util.concurrent;

import java.util.*;

class CopyOnWriteArrayList$COWSubListIterator implements ListIterator {
    
    /*synthetic*/ CopyOnWriteArrayList$COWSubListIterator(List x0, int x1, int x2, int x3, java.util.concurrent.CopyOnWriteArrayList$1 x4) {
        this(x0, x1, x2, x3);
    }
    private final ListIterator i;
    private final int index;
    private final int offset;
    private final int size;
    
    private CopyOnWriteArrayList$COWSubListIterator(List l, int index, int offset, int size) {
        
        this.index = index;
        this.offset = offset;
        this.size = size;
        i = l.listIterator(index + offset);
    }
    
    public boolean hasNext() {
        return nextIndex() < size;
    }
    
    public Object next() {
        if (hasNext()) return i.next(); else throw new NoSuchElementException();
    }
    
    public boolean hasPrevious() {
        return previousIndex() >= 0;
    }
    
    public Object previous() {
        if (hasPrevious()) return i.previous(); else throw new NoSuchElementException();
    }
    
    public int nextIndex() {
        return i.nextIndex() - offset;
    }
    
    public int previousIndex() {
        return i.previousIndex() - offset;
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
