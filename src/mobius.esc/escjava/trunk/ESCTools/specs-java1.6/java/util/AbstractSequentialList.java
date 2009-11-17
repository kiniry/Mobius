package java.util;

public abstract class AbstractSequentialList extends AbstractList {
    
    protected AbstractSequentialList() {
        
    }
    
    public Object get(int index) {
        ListIterator e = listIterator(index);
        try {
            return (e.next());
        } catch (NoSuchElementException exc) {
            throw (new IndexOutOfBoundsException("Index: " + index));
        }
    }
    
    public Object set(int index, Object element) {
        ListIterator e = listIterator(index);
        try {
            Object oldVal = e.next();
            e.set(element);
            return oldVal;
        } catch (NoSuchElementException exc) {
            throw (new IndexOutOfBoundsException("Index: " + index));
        }
    }
    
    public void add(int index, Object element) {
        ListIterator e = listIterator(index);
        e.add(element);
    }
    
    public Object remove(int index) {
        ListIterator e = listIterator(index);
        Object outCast;
        try {
            outCast = e.next();
        } catch (NoSuchElementException exc) {
            throw (new IndexOutOfBoundsException("Index: " + index));
        }
        e.remove();
        return (outCast);
    }
    
    public boolean addAll(int index, Collection c) {
        boolean modified = false;
        ListIterator e1 = listIterator(index);
        Iterator e2 = c.iterator();
        while (e2.hasNext()) {
            e1.add(e2.next());
            modified = true;
        }
        return modified;
    }
    
    public Iterator iterator() {
        return listIterator();
    }
    
    public abstract ListIterator listIterator(int index);
}
