package java.util;

class Collections$UnmodifiableList extends Collections$UnmodifiableCollection implements List {
    static final long serialVersionUID = -283967356065247728L;
    List list;
    
    Collections$UnmodifiableList(List list) {
        super(list);
        this.list = list;
    }
    
    public boolean equals(Object o) {
        return list.equals(o);
    }
    
    public int hashCode() {
        return list.hashCode();
    }
    
    public Object get(int index) {
        return list.get(index);
    }
    
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
        return list.indexOf(o);
    }
    
    public int lastIndexOf(Object o) {
        return list.lastIndexOf(o);
    }
    
    public boolean addAll(int index, Collection c) {
        throw new UnsupportedOperationException();
    }
    
    public ListIterator listIterator() {
        return listIterator(0);
    }
    
    public ListIterator listIterator(final int index) {
        return new Collections$UnmodifiableList$1(this, index);
    }
    
    public List subList(int fromIndex, int toIndex) {
        return new Collections$UnmodifiableList(list.subList(fromIndex, toIndex));
    }
    
    private Object readResolve() {
        return (list instanceof RandomAccess ? new Collections$UnmodifiableRandomAccessList(list) : this);
    }
}
