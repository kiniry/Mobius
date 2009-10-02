package java.util;

public abstract class AbstractList extends AbstractCollection implements List {
    {
    }
    
    protected AbstractList() {
        
    }
    
    public boolean add(Object o) {
        add(size(), o);
        return true;
    }
    
    public abstract Object get(int index);
    
    public Object set(int index, Object element) {
        throw new UnsupportedOperationException();
    }
    
    public void add(int index, Object element) {
        throw new UnsupportedOperationException();
    }
    
    public Object remove(int index) {
        throw new UnsupportedOperationException();
    }
    
    public int indexOf(Object o) {
        ListIterator e = listIterator();
        if (o == null) {
            while (e.hasNext()) if (e.next() == null) return e.previousIndex();
        } else {
            while (e.hasNext()) if (o.equals(e.next())) return e.previousIndex();
        }
        return -1;
    }
    
    public int lastIndexOf(Object o) {
        ListIterator e = listIterator(size());
        if (o == null) {
            while (e.hasPrevious()) if (e.previous() == null) return e.nextIndex();
        } else {
            while (e.hasPrevious()) if (o.equals(e.previous())) return e.nextIndex();
        }
        return -1;
    }
    
    public void clear() {
        removeRange(0, size());
    }
    
    public boolean addAll(int index, Collection c) {
        boolean modified = false;
        Iterator e = c.iterator();
        while (e.hasNext()) {
            add(index++, e.next());
            modified = true;
        }
        return modified;
    }
    
    public Iterator iterator() {
        return new AbstractList$Itr(this, null);
    }
    
    public ListIterator listIterator() {
        return listIterator(0);
    }
    
    public ListIterator listIterator(final int index) {
        if (index < 0 || index > size()) throw new IndexOutOfBoundsException("Index: " + index);
        return new AbstractList$ListItr(this, index);
    }
    {
    }
    {
    }
    
    public List subList(int fromIndex, int toIndex) {
        return (this instanceof RandomAccess ? new RandomAccessSubList(this, fromIndex, toIndex) : new SubList(this, fromIndex, toIndex));
    }
    
    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof List)) return false;
        ListIterator e1 = listIterator();
        ListIterator e2 = ((List)(List)o).listIterator();
        while (e1.hasNext() && e2.hasNext()) {
            Object o1 = e1.next();
            Object o2 = e2.next();
            if (!(o1 == null ? o2 == null : o1.equals(o2))) return false;
        }
        return !(e1.hasNext() || e2.hasNext());
    }
    
    public int hashCode() {
        int hashCode = 1;
        Iterator i = iterator();
        while (i.hasNext()) {
            Object obj = i.next();
            hashCode = 31 * hashCode + (obj == null ? 0 : obj.hashCode());
        }
        return hashCode;
    }
    
    protected void removeRange(int fromIndex, int toIndex) {
        ListIterator it = listIterator(fromIndex);
        for (int i = 0, n = toIndex - fromIndex; i < n; i++) {
            it.next();
            it.remove();
        }
    }
    protected transient int modCount = 0;
}
