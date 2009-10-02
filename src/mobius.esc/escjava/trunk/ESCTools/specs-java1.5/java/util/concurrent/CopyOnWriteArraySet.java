package java.util.concurrent;

import java.util.*;

public class CopyOnWriteArraySet extends AbstractSet implements java.io.Serializable {
    private static final long serialVersionUID = 5457747651344034263L;
    private final CopyOnWriteArrayList al;
    
    public CopyOnWriteArraySet() {
        
        al = new CopyOnWriteArrayList();
    }
    
    public CopyOnWriteArraySet(Collection c) {
        
        al = new CopyOnWriteArrayList();
        al.addAllAbsent(c);
    }
    
    public int size() {
        return al.size();
    }
    
    public boolean isEmpty() {
        return al.isEmpty();
    }
    
    public boolean contains(Object o) {
        return al.contains(o);
    }
    
    public Object[] toArray() {
        return al.toArray();
    }
    
    public Object[] toArray(Object[] a) {
        return al.toArray(a);
    }
    
    public void clear() {
        al.clear();
    }
    
    public Iterator iterator() {
        return al.iterator();
    }
    
    public boolean remove(Object o) {
        return al.remove(o);
    }
    
    public boolean add(Object o) {
        return al.addIfAbsent(o);
    }
    
    public boolean containsAll(Collection c) {
        return al.containsAll(c);
    }
    
    public boolean addAll(Collection c) {
        return al.addAllAbsent(c) > 0;
    }
    
    public boolean removeAll(Collection c) {
        return al.removeAll(c);
    }
    
    public boolean retainAll(Collection c) {
        return al.retainAll(c);
    }
}
