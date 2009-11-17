package java.util;

class Collections$CheckedList extends Collections$CheckedCollection implements List {
    static final long serialVersionUID = 65247728283967356L;
    final List list;
    
    Collections$CheckedList(List list, Class type) {
        super(list, type);
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
    
    public Object remove(int index) {
        return list.remove(index);
    }
    
    public int indexOf(Object o) {
        return list.indexOf(o);
    }
    
    public int lastIndexOf(Object o) {
        return list.lastIndexOf(o);
    }
    
    public Object set(int index, Object element) {
        typeCheck(element);
        return list.set(index, element);
    }
    
    public void add(int index, Object element) {
        typeCheck(element);
        list.add(index, element);
    }
    
    public boolean addAll(int index, Collection c) {
        Object[] a = null;
        try {
            a = c.toArray(zeroLengthElementArray());
        } catch (ArrayStoreException e) {
            throw new ClassCastException();
        }
        return list.addAll(index, Arrays.asList(a));
    }
    
    public ListIterator listIterator() {
        return listIterator(0);
    }
    
    public ListIterator listIterator(final int index) {
        return new Collections$CheckedList$1(this, index);
    }
    
    public List subList(int fromIndex, int toIndex) {
        return new Collections$CheckedList(list.subList(fromIndex, toIndex), type);
    }
}
