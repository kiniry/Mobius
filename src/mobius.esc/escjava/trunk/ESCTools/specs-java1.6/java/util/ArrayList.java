package java.util;

public class ArrayList extends AbstractList implements List, RandomAccess, Cloneable, java.io.Serializable {
    private static final long serialVersionUID = 8683452581122892189L;
    private transient Object[] elementData;
    private int size;
    
    public ArrayList(int initialCapacity) {
        
        if (initialCapacity < 0) throw new IllegalArgumentException("Illegal Capacity: " + initialCapacity);
        this.elementData = (Object[])new Object[initialCapacity];
    }
    
    public ArrayList() {
        this(10);
    }
    
    public ArrayList(Collection c) {
        
        size = c.size();
        int capacity = (int)Math.min((size * 110L) / 100, Integer.MAX_VALUE);
        elementData = (Object[])c.toArray(new Object[capacity]);
    }
    
    public void trimToSize() {
        modCount++;
        int oldCapacity = elementData.length;
        if (size < oldCapacity) {
            Object[] oldData = elementData;
            elementData = (Object[])new Object[size];
            System.arraycopy(oldData, 0, elementData, 0, size);
        }
    }
    
    public void ensureCapacity(int minCapacity) {
        modCount++;
        int oldCapacity = elementData.length;
        if (minCapacity > oldCapacity) {
            Object[] oldData = elementData;
            int newCapacity = (oldCapacity * 3) / 2 + 1;
            if (newCapacity < minCapacity) newCapacity = minCapacity;
            elementData = (Object[])new Object[newCapacity];
            System.arraycopy(oldData, 0, elementData, 0, size);
        }
    }
    
    public int size() {
        return size;
    }
    
    public boolean isEmpty() {
        return size == 0;
    }
    
    public boolean contains(Object elem) {
        return indexOf(elem) >= 0;
    }
    
    public int indexOf(Object elem) {
        if (elem == null) {
            for (int i = 0; i < size; i++) if (elementData[i] == null) return i;
        } else {
            for (int i = 0; i < size; i++) if (elem.equals(elementData[i])) return i;
        }
        return -1;
    }
    
    public int lastIndexOf(Object elem) {
        if (elem == null) {
            for (int i = size - 1; i >= 0; i--) if (elementData[i] == null) return i;
        } else {
            for (int i = size - 1; i >= 0; i--) if (elem.equals(elementData[i])) return i;
        }
        return -1;
    }
    
    public Object clone() {
        try {
            ArrayList v = (ArrayList)(ArrayList)super.clone();
            v.elementData = (Object[])new Object[size];
            System.arraycopy(elementData, 0, v.elementData, 0, size);
            v.modCount = 0;
            return v;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    public Object[] toArray() {
        Object[] result = new Object[size];
        System.arraycopy(elementData, 0, result, 0, size);
        return result;
    }
    
    public Object[] toArray(Object[] a) {
        if (a.length < size) a = (Object[])(Object[])java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), size);
        System.arraycopy(elementData, 0, a, 0, size);
        if (a.length > size) a[size] = null;
        return a;
    }
    
    public Object get(int index) {
        RangeCheck(index);
        return elementData[index];
    }
    
    public Object set(int index, Object element) {
        RangeCheck(index);
        Object oldValue = elementData[index];
        elementData[index] = element;
        return oldValue;
    }
    
    public boolean add(Object o) {
        ensureCapacity(size + 1);
        elementData[size++] = o;
        return true;
    }
    
    public void add(int index, Object element) {
        if (index > size || index < 0) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + size);
        ensureCapacity(size + 1);
        System.arraycopy(elementData, index, elementData, index + 1, size - index);
        elementData[index] = element;
        size++;
    }
    
    public Object remove(int index) {
        RangeCheck(index);
        modCount++;
        Object oldValue = elementData[index];
        int numMoved = size - index - 1;
        if (numMoved > 0) System.arraycopy(elementData, index + 1, elementData, index, numMoved);
        elementData[--size] = null;
        return oldValue;
    }
    
    public boolean remove(Object o) {
        if (o == null) {
            for (int index = 0; index < size; index++) if (elementData[index] == null) {
		    fastRemove(index);
		    return true;
		}
        } else {
            for (int index = 0; index < size; index++) if (o.equals(elementData[index])) {
		    fastRemove(index);
		    return true;
		}
        }
        return false;
    }
    
    private void fastRemove(int index) {
        modCount++;
        int numMoved = size - index - 1;
        if (numMoved > 0) System.arraycopy(elementData, index + 1, elementData, index, numMoved);
        elementData[--size] = null;
    }
    
    public void clear() {
        modCount++;
        for (int i = 0; i < size; i++) elementData[i] = null;
        size = 0;
    }
    
    public boolean addAll(Collection c) {
        Object[] a = c.toArray();
        int numNew = a.length;
        ensureCapacity(size + numNew);
        System.arraycopy(a, 0, elementData, size, numNew);
        size += numNew;
        return numNew != 0;
    }
    
    public boolean addAll(int index, Collection c) {
        if (index > size || index < 0) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + size);
        Object[] a = c.toArray();
        int numNew = a.length;
        ensureCapacity(size + numNew);
        int numMoved = size - index;
        if (numMoved > 0) System.arraycopy(elementData, index, elementData, index + numNew, numMoved);
        System.arraycopy(a, 0, elementData, index, numNew);
        size += numNew;
        return numNew != 0;
    }
    
    protected void removeRange(int fromIndex, int toIndex) {
        modCount++;
        int numMoved = size - toIndex;
        System.arraycopy(elementData, toIndex, elementData, fromIndex, numMoved);
        int newSize = size - (toIndex - fromIndex);
        while (size != newSize) elementData[--size] = null;
    }
    
    private void RangeCheck(int index) {
        if (index >= size) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + size);
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        int expectedModCount = modCount;
        s.defaultWriteObject();
        s.writeInt(elementData.length);
        for (int i = 0; i < size; i++) s.writeObject(elementData[i]);
        if (modCount != expectedModCount) {
            throw new ConcurrentModificationException();
        }
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        int arrayLength = s.readInt();
        Object[] a = elementData = (Object[])new Object[arrayLength];
        for (int i = 0; i < size; i++) a[i] = s.readObject();
    }
}
