package java.util;

class SubList extends AbstractList {
    
    /*synthetic*/ static int access$302(SubList x0, int x1) {
        return x0.expectedModCount = x1;
    }
    
    /*synthetic*/ static int access$210(SubList x0) {
        return x0.size--;
    }
    
    /*synthetic*/ static int access$208(SubList x0) {
        return x0.size++;
    }
    
    /*synthetic*/ static int access$200(SubList x0) {
        return x0.size;
    }
    
    /*synthetic*/ static AbstractList access$100(SubList x0) {
        return x0.l;
    }
    
    /*synthetic*/ static int access$000(SubList x0) {
        return x0.offset;
    }
    private AbstractList l;
    private int offset;
    private int size;
    private int expectedModCount;
    
    SubList(AbstractList list, int fromIndex, int toIndex) {
        
        if (fromIndex < 0) throw new IndexOutOfBoundsException("fromIndex = " + fromIndex);
        if (toIndex > list.size()) throw new IndexOutOfBoundsException("toIndex = " + toIndex);
        if (fromIndex > toIndex) throw new IllegalArgumentException("fromIndex(" + fromIndex + ") > toIndex(" + toIndex + ")");
        l = list;
        offset = fromIndex;
        size = toIndex - fromIndex;
        expectedModCount = l.modCount;
    }
    
    public Object set(int index, Object element) {
        rangeCheck(index);
        checkForComodification();
        return l.set(index + offset, element);
    }
    
    public Object get(int index) {
        rangeCheck(index);
        checkForComodification();
        return l.get(index + offset);
    }
    
    public int size() {
        checkForComodification();
        return size;
    }
    
    public void add(int index, Object element) {
        if (index < 0 || index > size) throw new IndexOutOfBoundsException();
        checkForComodification();
        l.add(index + offset, element);
        expectedModCount = l.modCount;
        size++;
        modCount++;
    }
    
    public Object remove(int index) {
        rangeCheck(index);
        checkForComodification();
        Object result = l.remove(index + offset);
        expectedModCount = l.modCount;
        size--;
        modCount++;
        return result;
    }
    
    protected void removeRange(int fromIndex, int toIndex) {
        checkForComodification();
        l.removeRange(fromIndex + offset, toIndex + offset);
        expectedModCount = l.modCount;
        size -= (toIndex - fromIndex);
        modCount++;
    }
    
    public boolean addAll(Collection c) {
        return addAll(size, c);
    }
    
    public boolean addAll(int index, Collection c) {
        if (index < 0 || index > size) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + size);
        int cSize = c.size();
        if (cSize == 0) return false;
        checkForComodification();
        l.addAll(offset + index, c);
        expectedModCount = l.modCount;
        size += cSize;
        modCount++;
        return true;
    }
    
    public Iterator iterator() {
        return listIterator();
    }
    
    public ListIterator listIterator(final int index) {
        checkForComodification();
        if (index < 0 || index > size) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + size);
        return new SubList$1(this, index);
    }
    
    public List subList(int fromIndex, int toIndex) {
        return new SubList(this, fromIndex, toIndex);
    }
    
    private void rangeCheck(int index) {
        if (index < 0 || index >= size) throw new IndexOutOfBoundsException("Index: " + index + ",Size: " + size);
    }
    
    private void checkForComodification() {
        if (l.modCount != expectedModCount) throw new ConcurrentModificationException();
    }
}
