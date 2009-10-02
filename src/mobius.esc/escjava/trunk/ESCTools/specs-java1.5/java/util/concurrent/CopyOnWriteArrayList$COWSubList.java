package java.util.concurrent;

import java.util.*;

class CopyOnWriteArrayList$COWSubList extends AbstractList {
    
    /*synthetic*/ CopyOnWriteArrayList$COWSubList(CopyOnWriteArrayList x0, int x1, int x2, java.util.concurrent.CopyOnWriteArrayList$1 x3) {
        this(x0, x1, x2);
    }
    private final CopyOnWriteArrayList l;
    private final int offset;
    private int size;
    private Object[] expectedArray;
    
    private CopyOnWriteArrayList$COWSubList(CopyOnWriteArrayList list, int fromIndex, int toIndex) {
        
        l = list;
        expectedArray = CopyOnWriteArrayList.access$200(l);
        offset = fromIndex;
        size = toIndex - fromIndex;
    }
    
    private void checkForComodification() {
        if (CopyOnWriteArrayList.access$300(l) != expectedArray) throw new ConcurrentModificationException();
    }
    
    private void rangeCheck(int index) {
        if (index < 0 || index >= size) throw new IndexOutOfBoundsException("Index: " + index + ",Size: " + size);
    }
    
    public Object set(int index, Object element) {
        synchronized (l) {
            rangeCheck(index);
            checkForComodification();
            Object x = l.set(index + offset, element);
            expectedArray = CopyOnWriteArrayList.access$300(l);
            return x;
        }
    }
    
    public Object get(int index) {
        synchronized (l) {
            rangeCheck(index);
            checkForComodification();
            return l.get(index + offset);
        }
    }
    
    public int size() {
        synchronized (l) {
            checkForComodification();
            return size;
        }
    }
    
    public void add(int index, Object element) {
        synchronized (l) {
            checkForComodification();
            if (index < 0 || index > size) throw new IndexOutOfBoundsException();
            l.add(index + offset, element);
            expectedArray = CopyOnWriteArrayList.access$300(l);
            size++;
        }
    }
    
    public void clear() {
        synchronized (l) {
            checkForComodification();
            CopyOnWriteArrayList.access$400(l, offset, offset + size);
            expectedArray = CopyOnWriteArrayList.access$300(l);
            size = 0;
        }
    }
    
    public Object remove(int index) {
        synchronized (l) {
            rangeCheck(index);
            checkForComodification();
            Object result = l.remove(index + offset);
            expectedArray = CopyOnWriteArrayList.access$300(l);
            size--;
            return result;
        }
    }
    
    public Iterator iterator() {
        synchronized (l) {
            checkForComodification();
            return new CopyOnWriteArrayList$COWSubListIterator(l, 0, offset, size, null);
        }
    }
    
    public ListIterator listIterator(final int index) {
        synchronized (l) {
            checkForComodification();
            if (index < 0 || index > size) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + size);
            return new CopyOnWriteArrayList$COWSubListIterator(l, index, offset, size, null);
        }
    }
    
    public List subList(int fromIndex, int toIndex) {
        synchronized (l) {
            checkForComodification();
            if (fromIndex < 0 || toIndex > size) throw new IndexOutOfBoundsException();
            return new CopyOnWriteArrayList$COWSubList(l, fromIndex + offset, toIndex + offset);
        }
    }
}
