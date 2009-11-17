package java.util.concurrent;

import java.util.*;

class CopyOnWriteArrayList$COWIterator implements ListIterator {
    
    /*synthetic*/ CopyOnWriteArrayList$COWIterator(Object[] x0, int x1, java.util.concurrent.CopyOnWriteArrayList$1 x2) {
        this(x0, x1);
    }
    private final Object[] array;
    private int cursor;
    
    private CopyOnWriteArrayList$COWIterator(Object[] elementArray, int initialCursor) {
        
        array = elementArray;
        cursor = initialCursor;
    }
    
    public boolean hasNext() {
        return cursor < array.length;
    }
    
    public boolean hasPrevious() {
        return cursor > 0;
    }
    
    public Object next() {
        try {
            return array[cursor++];
        } catch (IndexOutOfBoundsException ex) {
            throw new NoSuchElementException();
        }
    }
    
    public Object previous() {
        try {
            return array[--cursor];
        } catch (IndexOutOfBoundsException e) {
            throw new NoSuchElementException();
        }
    }
    
    public int nextIndex() {
        return cursor;
    }
    
    public int previousIndex() {
        return cursor - 1;
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
