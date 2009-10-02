package java.util;

import java.io.Serializable;
import java.io.ObjectOutputStream;
import java.io.IOException;

class Collections$SynchronizedCollection implements Collection, Serializable {
    private static final long serialVersionUID = 3053995032091335093L;
    Collection c;
    Object mutex;
    
    Collections$SynchronizedCollection(Collection c) {
        
        if (c == null) throw new NullPointerException();
        this.c = c;
        mutex = this;
    }
    
    Collections$SynchronizedCollection(Collection c, Object mutex) {
        
        this.c = c;
        this.mutex = mutex;
    }
    
    public int size() {
        synchronized (mutex) {
            return c.size();
        }
    }
    
    public boolean isEmpty() {
        synchronized (mutex) {
            return c.isEmpty();
        }
    }
    
    public boolean contains(Object o) {
        synchronized (mutex) {
            return c.contains(o);
        }
    }
    
    public Object[] toArray() {
        synchronized (mutex) {
            return c.toArray();
        }
    }
    
    public Object[] toArray(Object[] a) {
        synchronized (mutex) {
            return c.toArray(a);
        }
    }
    
    public Iterator iterator() {
        return c.iterator();
    }
    
    public boolean add(Object o) {
        synchronized (mutex) {
            return c.add(o);
        }
    }
    
    public boolean remove(Object o) {
        synchronized (mutex) {
            return c.remove(o);
        }
    }
    
    public boolean containsAll(Collection coll) {
        synchronized (mutex) {
            return c.containsAll(coll);
        }
    }
    
    public boolean addAll(Collection coll) {
        synchronized (mutex) {
            return c.addAll(coll);
        }
    }
    
    public boolean removeAll(Collection coll) {
        synchronized (mutex) {
            return c.removeAll(coll);
        }
    }
    
    public boolean retainAll(Collection coll) {
        synchronized (mutex) {
            return c.retainAll(coll);
        }
    }
    
    public void clear() {
        synchronized (mutex) {
            c.clear();
        }
    }
    
    public String toString() {
        synchronized (mutex) {
            return c.toString();
        }
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        synchronized (mutex) {
            s.defaultWriteObject();
        }
    }
}
