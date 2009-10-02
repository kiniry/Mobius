package java.util;

public class LinkedList extends AbstractSequentialList implements List, Queue, Cloneable, java.io.Serializable {
    
    /*synthetic*/ static LinkedList$Entry access$300(LinkedList x0, Object x1, LinkedList$Entry x2) {
        return x0.addBefore(x1, x2);
    }
    
    /*synthetic*/ static Object access$200(LinkedList x0, LinkedList$Entry x1) {
        return x0.remove(x1);
    }
    
    /*synthetic*/ static int access$100(LinkedList x0) {
        return x0.size;
    }
    
    /*synthetic*/ static LinkedList$Entry access$000(LinkedList x0) {
        return x0.header;
    }
    private transient LinkedList$Entry header = new LinkedList$Entry(null, null, null);
    private transient int size = 0;
    
    public LinkedList() {
        
        header.next = header.previous = header;
    }
    
    public LinkedList(Collection c) {
        this();
        addAll(c);
    }
    
    public Object getFirst() {
        if (size == 0) throw new NoSuchElementException();
        return header.next.element;
    }
    
    public Object getLast() {
        if (size == 0) throw new NoSuchElementException();
        return header.previous.element;
    }
    
    public Object removeFirst() {
        return remove(header.next);
    }
    
    public Object removeLast() {
        return remove(header.previous);
    }
    
    public void addFirst(Object o) {
        addBefore(o, header.next);
    }
    
    public void addLast(Object o) {
        addBefore(o, header);
    }
    
    public boolean contains(Object o) {
        return indexOf(o) != -1;
    }
    
    public int size() {
        return size;
    }
    
    public boolean add(Object o) {
        addBefore(o, header);
        return true;
    }
    
    public boolean remove(Object o) {
        if (o == null) {
            for (LinkedList$Entry e = header.next; e != header; e = e.next) {
                if (e.element == null) {
                    remove(e);
                    return true;
                }
            }
        } else {
            for (LinkedList$Entry e = header.next; e != header; e = e.next) {
                if (o.equals(e.element)) {
                    remove(e);
                    return true;
                }
            }
        }
        return false;
    }
    
    public boolean addAll(Collection c) {
        return addAll(size, c);
    }
    
    public boolean addAll(int index, Collection c) {
        if (index < 0 || index > size) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + size);
        Object[] a = c.toArray();
        int numNew = a.length;
        if (numNew == 0) return false;
        modCount++;
        LinkedList$Entry successor = (index == size ? header : entry(index));
        LinkedList$Entry predecessor = successor.previous;
        for (int i = 0; i < numNew; i++) {
            LinkedList$Entry e = new LinkedList$Entry((Object)a[i], successor, predecessor);
            predecessor.next = e;
            predecessor = e;
        }
        successor.previous = predecessor;
        size += numNew;
        return true;
    }
    
    public void clear() {
        LinkedList$Entry e = header.next;
        while (e != header) {
            LinkedList$Entry next = e.next;
            e.next = e.previous = null;
            e.element = null;
            e = next;
        }
        header.next = header.previous = header;
        size = 0;
        modCount++;
    }
    
    public Object get(int index) {
        return entry(index).element;
    }
    
    public Object set(int index, Object element) {
        LinkedList$Entry e = entry(index);
        Object oldVal = e.element;
        e.element = element;
        return oldVal;
    }
    
    public void add(int index, Object element) {
        addBefore(element, (index == size ? header : entry(index)));
    }
    
    public Object remove(int index) {
        return remove(entry(index));
    }
    
    private LinkedList$Entry entry(int index) {
        if (index < 0 || index >= size) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + size);
        LinkedList$Entry e = header;
        if (index < (size >> 1)) {
            for (int i = 0; i <= index; i++) e = e.next;
        } else {
            for (int i = size; i > index; i--) e = e.previous;
        }
        return e;
    }
    
    public int indexOf(Object o) {
        int index = 0;
        if (o == null) {
            for (LinkedList$Entry e = header.next; e != header; e = e.next) {
                if (e.element == null) return index;
                index++;
            }
        } else {
            for (LinkedList$Entry e = header.next; e != header; e = e.next) {
                if (o.equals(e.element)) return index;
                index++;
            }
        }
        return -1;
    }
    
    public int lastIndexOf(Object o) {
        int index = size;
        if (o == null) {
            for (LinkedList$Entry e = header.previous; e != header; e = e.previous) {
                index--;
                if (e.element == null) return index;
            }
        } else {
            for (LinkedList$Entry e = header.previous; e != header; e = e.previous) {
                index--;
                if (o.equals(e.element)) return index;
            }
        }
        return -1;
    }
    
    public Object peek() {
        if (size == 0) return null;
        return getFirst();
    }
    
    public Object element() {
        return getFirst();
    }
    
    public Object poll() {
        if (size == 0) return null;
        return removeFirst();
    }
    
    public Object remove() {
        return removeFirst();
    }
    
    public boolean offer(Object o) {
        return add(o);
    }
    
    public ListIterator listIterator(int index) {
        return new LinkedList$ListItr(this, index);
    }
    {
    }
    {
    }
    
    private LinkedList$Entry addBefore(Object o, LinkedList$Entry e) {
        LinkedList$Entry newEntry = new LinkedList$Entry(o, e, e.previous);
        newEntry.previous.next = newEntry;
        newEntry.next.previous = newEntry;
        size++;
        modCount++;
        return newEntry;
    }
    
    private Object remove(LinkedList$Entry e) {
        if (e == header) throw new NoSuchElementException();
        Object result = e.element;
        e.previous.next = e.next;
        e.next.previous = e.previous;
        e.next = e.previous = null;
        e.element = null;
        size--;
        modCount++;
        return result;
    }
    
    public Object clone() {
        LinkedList clone = null;
        try {
            clone = (LinkedList)(LinkedList)super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
        clone.header = new LinkedList$Entry(null, null, null);
        clone.header.next = clone.header.previous = clone.header;
        clone.size = 0;
        clone.modCount = 0;
        for (LinkedList$Entry e = header.next; e != header; e = e.next) clone.add(e.element);
        return clone;
    }
    
    public Object[] toArray() {
        Object[] result = new Object[size];
        int i = 0;
        for (LinkedList$Entry e = header.next; e != header; e = e.next) result[i++] = e.element;
        return result;
    }
    
    public Object[] toArray(Object[] a) {
        if (a.length < size) a = (Object[])(Object[])java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), size);
        int i = 0;
        Object[] result = a;
        for (LinkedList$Entry e = header.next; e != header; e = e.next) result[i++] = e.element;
        if (a.length > size) a[size] = null;
        return a;
    }
    private static final long serialVersionUID = 876323262645176354L;
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        s.defaultWriteObject();
        s.writeInt(size);
        for (LinkedList$Entry e = header.next; e != header; e = e.next) s.writeObject(e.element);
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        int size = s.readInt();
        header = new LinkedList$Entry(null, null, null);
        header.next = header.previous = header;
        for (int i = 0; i < size; i++) addBefore((Object)s.readObject(), header);
    }
}
