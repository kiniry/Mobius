package java.util;

class Collections$SynchronizedList extends Collections$SynchronizedCollection implements List {
    static final long serialVersionUID = -7754090372962971524L;
    List list;
    
    Collections$SynchronizedList(List list) {
        super(list);
        this.list = list;
    }
    
    Collections$SynchronizedList(List list, Object mutex) {
        super(list, mutex);
        this.list = list;
    }
    
    public boolean equals(Object o) {
        synchronized (mutex) {
            return list.equals(o);
        }
    }
    
    public int hashCode() {
        synchronized (mutex) {
            return list.hashCode();
        }
    }
    
    public Object get(int index) {
        synchronized (mutex) {
            return list.get(index);
        }
    }
    
    public Object set(int index, Object element) {
        synchronized (mutex) {
            return list.set(index, element);
        }
    }
    
    public void add(int index, Object element) {
        synchronized (mutex) {
            list.add(index, element);
        }
    }
    
    public Object remove(int index) {
        synchronized (mutex) {
            return list.remove(index);
        }
    }
    
    public int indexOf(Object o) {
        synchronized (mutex) {
            return list.indexOf(o);
        }
    }
    
    public int lastIndexOf(Object o) {
        synchronized (mutex) {
            return list.lastIndexOf(o);
        }
    }
    
    public boolean addAll(int index, Collection c) {
        synchronized (mutex) {
            return list.addAll(index, c);
        }
    }
    
    public ListIterator listIterator() {
        return list.listIterator();
    }
    
    public ListIterator listIterator(int index) {
        return list.listIterator(index);
    }
    
    public List subList(int fromIndex, int toIndex) {
        synchronized (mutex) {
            return new Collections$SynchronizedList(list.subList(fromIndex, toIndex), mutex);
        }
    }
    
    private Object readResolve() {
        return (list instanceof RandomAccess ? new Collections$SynchronizedRandomAccessList(list) : this);
    }
}
