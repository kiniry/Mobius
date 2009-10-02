package java.util;

import java.io.Serializable;

class Collections$UnmodifiableCollection implements Collection, Serializable {
    private static final long serialVersionUID = 1820017752578914078L;
    Collection c;
    
    Collections$UnmodifiableCollection(Collection c) {
        
        if (c == null) throw new NullPointerException();
        this.c = c;
    }
    
    public int size() {
        return c.size();
    }
    
    public boolean isEmpty() {
        return c.isEmpty();
    }
    
    public boolean contains(Object o) {
        return c.contains(o);
    }
    
    public Object[] toArray() {
        return c.toArray();
    }
    
    public Object[] toArray(Object[] a) {
        return c.toArray(a);
    }
    
    public String toString() {
        return c.toString();
    }
    
    public Iterator iterator() {
        return new Collections$UnmodifiableCollection$1(this);
    }
    
    public boolean add(Object o) {
        throw new UnsupportedOperationException();
    }
    
    public boolean remove(Object o) {
        throw new UnsupportedOperationException();
    }
    
    public boolean containsAll(Collection coll) {
        return c.containsAll(coll);
    }
    
    public boolean addAll(Collection coll) {
        throw new UnsupportedOperationException();
    }
    
    public boolean removeAll(Collection coll) {
        throw new UnsupportedOperationException();
    }
    
    public boolean retainAll(Collection coll) {
        throw new UnsupportedOperationException();
    }
    
    public void clear() {
        throw new UnsupportedOperationException();
    }
}
