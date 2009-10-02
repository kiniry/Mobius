package java.util;

class Collections$SynchronizedRandomAccessList extends Collections$SynchronizedList implements RandomAccess {
    
    Collections$SynchronizedRandomAccessList(List list) {
        super(list);
    }
    
    Collections$SynchronizedRandomAccessList(List list, Object mutex) {
        super(list, mutex);
    }
    
    public List subList(int fromIndex, int toIndex) {
        synchronized (mutex) {
            return new Collections$SynchronizedRandomAccessList(list.subList(fromIndex, toIndex), mutex);
        }
    }
    static final long serialVersionUID = 1530674583602358482L;
    
    private Object writeReplace() {
        return new Collections$SynchronizedList(list);
    }
}
