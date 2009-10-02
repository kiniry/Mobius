package java.util;

public class PriorityQueue extends AbstractQueue implements java.io.Serializable {
    
    /*synthetic*/ static Object access$400(PriorityQueue x0, int x1) {
        return x0.removeAt(x1);
    }
    
    /*synthetic*/ static Object[] access$300(PriorityQueue x0) {
        return x0.queue;
    }
    
    /*synthetic*/ static int access$200(PriorityQueue x0) {
        return x0.size;
    }
    
    /*synthetic*/ static int access$100(PriorityQueue x0) {
        return x0.modCount;
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !PriorityQueue.class.desiredAssertionStatus();
    {
    }
    private static final long serialVersionUID = -7720805057305804111L;
    private static final int DEFAULT_INITIAL_CAPACITY = 11;
    private transient Object[] queue;
    private int size = 0;
    private final Comparator comparator;
    private transient int modCount = 0;
    
    public PriorityQueue() {
        this(DEFAULT_INITIAL_CAPACITY, null);
    }
    
    public PriorityQueue(int initialCapacity) {
        this(initialCapacity, null);
    }
    
    public PriorityQueue(int initialCapacity, Comparator comparator) {
        
        if (initialCapacity < 1) throw new IllegalArgumentException();
        this.queue = new Object[initialCapacity + 1];
        this.comparator = comparator;
    }
    
    private void initializeArray(Collection c) {
        int sz = c.size();
        int initialCapacity = (int)Math.min((sz * 110L) / 100, Integer.MAX_VALUE - 1);
        if (initialCapacity < 1) initialCapacity = 1;
        this.queue = new Object[initialCapacity + 1];
    }
    
    private void fillFromSorted(Collection c) {
        for (Iterator i = c.iterator(); i.hasNext(); ) queue[++size] = i.next();
    }
    
    private void fillFromUnsorted(Collection c) {
        for (Iterator i = c.iterator(); i.hasNext(); ) queue[++size] = i.next();
        heapify();
    }
    
    public PriorityQueue(Collection c) {
        
        initializeArray(c);
        if (c instanceof SortedSet) {
            SortedSet s = (SortedSet)(SortedSet)c;
            comparator = (Comparator)s.comparator();
            fillFromSorted(s);
        } else if (c instanceof PriorityQueue) {
            PriorityQueue s = (PriorityQueue)(PriorityQueue)c;
            comparator = (Comparator)s.comparator();
            fillFromSorted(s);
        } else {
            comparator = null;
            fillFromUnsorted(c);
        }
    }
    
    public PriorityQueue(PriorityQueue c) {
        
        initializeArray(c);
        comparator = (Comparator)c.comparator();
        fillFromSorted(c);
    }
    
    public PriorityQueue(SortedSet c) {
        
        initializeArray(c);
        comparator = (Comparator)c.comparator();
        fillFromSorted(c);
    }
    
    private void grow(int index) {
        int newlen = queue.length;
        if (index < newlen) return;
        if (index == Integer.MAX_VALUE) throw new OutOfMemoryError();
        while (newlen <= index) {
            if (newlen >= Integer.MAX_VALUE / 2) newlen = Integer.MAX_VALUE; else newlen <<= 2;
        }
        Object[] newQueue = new Object[newlen];
        System.arraycopy(queue, 0, newQueue, 0, queue.length);
        queue = newQueue;
    }
    
    public boolean offer(Object o) {
        if (o == null) throw new NullPointerException();
        modCount++;
        ++size;
        if (size >= queue.length) grow(size);
        queue[size] = o;
        fixUp(size);
        return true;
    }
    
    public Object peek() {
        if (size == 0) return null;
        return (Object)queue[1];
    }
    
    public boolean add(Object o) {
        return offer(o);
    }
    
    public boolean remove(Object o) {
        if (o == null) return false;
        if (comparator == null) {
            for (int i = 1; i <= size; i++) {
                if (((Comparable)(Comparable)queue[i]).compareTo((Object)o) == 0) {
                    removeAt(i);
                    return true;
                }
            }
        } else {
            for (int i = 1; i <= size; i++) {
                if (comparator.compare((Object)queue[i], (Object)o) == 0) {
                    removeAt(i);
                    return true;
                }
            }
        }
        return false;
    }
    
    public Iterator iterator() {
        return new PriorityQueue$Itr(this, null);
    }
    {
    }
    
    public int size() {
        return size;
    }
    
    public void clear() {
        modCount++;
        for (int i = 1; i <= size; i++) queue[i] = null;
        size = 0;
    }
    
    public Object poll() {
        if (size == 0) return null;
        modCount++;
        Object result = (Object)queue[1];
        queue[1] = queue[size];
        queue[size--] = null;
        if (size > 1) fixDown(1);
        return result;
    }
    
    private Object removeAt(int i) {
        if (!$assertionsDisabled && !(i > 0 && i <= size)) throw new AssertionError();
        modCount++;
        Object moved = (Object)queue[size];
        queue[i] = moved;
        queue[size--] = null;
        if (i <= size) {
            fixDown(i);
            if (queue[i] == moved) {
                fixUp(i);
                if (queue[i] != moved) return moved;
            }
        }
        return null;
    }
    
    private void fixUp(int k) {
        if (comparator == null) {
            while (k > 1) {
                int j = k >> 1;
                if (((Comparable)(Comparable)queue[j]).compareTo((Object)queue[k]) <= 0) break;
                Object tmp = queue[j];
                queue[j] = queue[k];
                queue[k] = tmp;
                k = j;
            }
        } else {
            while (k > 1) {
                int j = k >>> 1;
                if (comparator.compare((Object)queue[j], (Object)queue[k]) <= 0) break;
                Object tmp = queue[j];
                queue[j] = queue[k];
                queue[k] = tmp;
                k = j;
            }
        }
    }
    
    private void fixDown(int k) {
        int j;
        if (comparator == null) {
            while ((j = k << 1) <= size && (j > 0)) {
                if (j < size && ((Comparable)(Comparable)queue[j]).compareTo((Object)queue[j + 1]) > 0) j++;
                if (((Comparable)(Comparable)queue[k]).compareTo((Object)queue[j]) <= 0) break;
                Object tmp = queue[j];
                queue[j] = queue[k];
                queue[k] = tmp;
                k = j;
            }
        } else {
            while ((j = k << 1) <= size && (j > 0)) {
                if (j < size && comparator.compare((Object)queue[j], (Object)queue[j + 1]) > 0) j++;
                if (comparator.compare((Object)queue[k], (Object)queue[j]) <= 0) break;
                Object tmp = queue[j];
                queue[j] = queue[k];
                queue[k] = tmp;
                k = j;
            }
        }
    }
    
    private void heapify() {
        for (int i = size / 2; i >= 1; i--) fixDown(i);
    }
    
    public Comparator comparator() {
        return comparator;
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        s.defaultWriteObject();
        s.writeInt(queue.length);
        for (int i = 1; i <= size; i++) s.writeObject(queue[i]);
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        int arrayLength = s.readInt();
        queue = new Object[arrayLength];
        for (int i = 1; i <= size; i++) queue[i] = (Object)s.readObject();
    }
}
