package java.util;

public abstract class AbstractQueue extends AbstractCollection implements Queue {
    
    protected AbstractQueue() {
        
    }
    
    public boolean add(Object o) {
        if (offer(o)) return true; else throw new IllegalStateException("Queue full");
    }
    
    public Object remove() {
        Object x = poll();
        if (x != null) return x; else throw new NoSuchElementException();
    }
    
    public Object element() {
        Object x = peek();
        if (x != null) return x; else throw new NoSuchElementException();
    }
    
    public void clear() {
        while (poll() != null) ;
    }
    
    public boolean addAll(Collection c) {
        if (c == null) throw new NullPointerException();
        if (c == this) throw new IllegalArgumentException();
        boolean modified = false;
        Iterator e = c.iterator();
        while (e.hasNext()) {
            if (add(e.next())) modified = true;
        }
        return modified;
    }
}
