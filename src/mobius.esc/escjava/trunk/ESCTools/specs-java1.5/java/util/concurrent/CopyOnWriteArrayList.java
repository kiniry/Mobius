package java.util.concurrent;

import java.util.*;

public class CopyOnWriteArrayList implements List, RandomAccess, Cloneable, java.io.Serializable {
    
    /*synthetic*/ static void access$400(CopyOnWriteArrayList x0, int x1, int x2) {
        x0.removeRange(x1, x2);
    }
    
    /*synthetic*/ static Object[] access$300(CopyOnWriteArrayList x0) {
        return x0.array;
    }
    
    /*synthetic*/ static Object[] access$200(CopyOnWriteArrayList x0) {
        return x0.array();
    }
    {
    }
    private static final long serialVersionUID = 8673264195747942595L;
    private volatile transient Object[] array;
    
    private Object[] array() {
        return array;
    }
    
    public CopyOnWriteArrayList() {
        
        array = (Object[])new Object[0];
    }
    
    public CopyOnWriteArrayList(Collection c) {
        
        array = (Object[])new Object[c.size()];
        Iterator i = c.iterator();
        int size = 0;
        while (i.hasNext()) array[size++] = i.next();
    }
    
    public CopyOnWriteArrayList(Object[] toCopyIn) {
        
        copyIn(toCopyIn, 0, toCopyIn.length);
    }
    
    private synchronized void copyIn(Object[] toCopyIn, int first, int n) {
        array = (Object[])new Object[n];
        System.arraycopy(toCopyIn, first, array, 0, n);
    }
    
    public int size() {
        return array().length;
    }
    
    public boolean isEmpty() {
        return size() == 0;
    }
    
    public boolean contains(Object elem) {
        Object[] elementData = array();
        int len = elementData.length;
        return indexOf(elem, elementData, len) >= 0;
    }
    
    public int indexOf(Object elem) {
        Object[] elementData = array();
        int len = elementData.length;
        return indexOf(elem, elementData, len);
    }
    
    private static int indexOf(Object elem, Object[] elementData, int len) {
        if (elem == null) {
            for (int i = 0; i < len; i++) if (elementData[i] == null) return i;
        } else {
            for (int i = 0; i < len; i++) if (elem.equals(elementData[i])) return i;
        }
        return -1;
    }
    
    public int indexOf(Object elem, int index) {
        Object[] elementData = array();
        int elementCount = elementData.length;
        if (elem == null) {
            for (int i = index; i < elementCount; i++) if (elementData[i] == null) return i;
        } else {
            for (int i = index; i < elementCount; i++) if (elem.equals(elementData[i])) return i;
        }
        return -1;
    }
    
    public int lastIndexOf(Object elem) {
        Object[] elementData = array();
        int len = elementData.length;
        return lastIndexOf(elem, elementData, len);
    }
    
    private static int lastIndexOf(Object elem, Object[] elementData, int len) {
        if (elem == null) {
            for (int i = len - 1; i >= 0; i--) if (elementData[i] == null) return i;
        } else {
            for (int i = len - 1; i >= 0; i--) if (elem.equals(elementData[i])) return i;
        }
        return -1;
    }
    
    public int lastIndexOf(Object elem, int index) {
        Object[] elementData = array();
        if (elem == null) {
            for (int i = index; i >= 0; i--) if (elementData[i] == null) return i;
        } else {
            for (int i = index; i >= 0; i--) if (elem.equals(elementData[i])) return i;
        }
        return -1;
    }
    
    public Object clone() {
        try {
            Object[] elementData = array();
            CopyOnWriteArrayList v = (CopyOnWriteArrayList)(CopyOnWriteArrayList)super.clone();
            v.array = (Object[])new Object[elementData.length];
            System.arraycopy(elementData, 0, v.array, 0, elementData.length);
            return v;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    public Object[] toArray() {
        Object[] elementData = array();
        Object[] result = new Object[elementData.length];
        System.arraycopy(elementData, 0, result, 0, elementData.length);
        return result;
    }
    
    public Object[] toArray(Object[] a) {
        Object[] elementData = array();
        if (a.length < elementData.length) a = (Object[])(Object[])java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), elementData.length);
        System.arraycopy(elementData, 0, a, 0, elementData.length);
        if (a.length > elementData.length) a[elementData.length] = null;
        return a;
    }
    
    public Object get(int index) {
        Object[] elementData = array();
        rangeCheck(index, elementData.length);
        return elementData[index];
    }
    
    public synchronized Object set(int index, Object element) {
        int len = array.length;
        rangeCheck(index, len);
        Object oldValue = array[index];
        boolean same = (oldValue == element || (element != null && element.equals(oldValue)));
        if (!same) {
            Object[] newArray = (Object[])new Object[len];
            System.arraycopy(array, 0, newArray, 0, len);
            newArray[index] = element;
            array = newArray;
        }
        return oldValue;
    }
    
    public synchronized boolean add(Object element) {
        int len = array.length;
        Object[] newArray = (Object[])new Object[len + 1];
        System.arraycopy(array, 0, newArray, 0, len);
        newArray[len] = element;
        array = newArray;
        return true;
    }
    
    public synchronized void add(int index, Object element) {
        int len = array.length;
        if (index > len || index < 0) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + len);
        Object[] newArray = (Object[])new Object[len + 1];
        System.arraycopy(array, 0, newArray, 0, index);
        newArray[index] = element;
        System.arraycopy(array, index, newArray, index + 1, len - index);
        array = newArray;
    }
    
    public synchronized Object remove(int index) {
        int len = array.length;
        rangeCheck(index, len);
        Object oldValue = array[index];
        Object[] newArray = (Object[])new Object[len - 1];
        System.arraycopy(array, 0, newArray, 0, index);
        int numMoved = len - index - 1;
        if (numMoved > 0) System.arraycopy(array, index + 1, newArray, index, numMoved);
        array = newArray;
        return oldValue;
    }
    
    public synchronized boolean remove(Object o) {
        int len = array.length;
        if (len == 0) return false;
        int newlen = len - 1;
        Object[] newArray = (Object[])new Object[newlen];
        for (int i = 0; i < newlen; ++i) {
            if (o == array[i] || (o != null && o.equals(array[i]))) {
                for (int k = i + 1; k < len; ++k) newArray[k - 1] = array[k];
                array = newArray;
                return true;
            } else newArray[i] = array[i];
        }
        if (o == array[newlen] || (o != null && o.equals(array[newlen]))) {
            array = newArray;
            return true;
        } else return false;
    }
    
    private synchronized void removeRange(int fromIndex, int toIndex) {
        int len = array.length;
        if (fromIndex < 0 || fromIndex >= len || toIndex > len || toIndex < fromIndex) throw new IndexOutOfBoundsException();
        int numMoved = len - toIndex;
        int newlen = len - (toIndex - fromIndex);
        Object[] newArray = (Object[])new Object[newlen];
        System.arraycopy(array, 0, newArray, 0, fromIndex);
        System.arraycopy(array, toIndex, newArray, fromIndex, numMoved);
        array = newArray;
    }
    
    public synchronized boolean addIfAbsent(Object element) {
        int len = array.length;
        Object[] newArray = (Object[])new Object[len + 1];
        for (int i = 0; i < len; ++i) {
            if (element == array[i] || (element != null && element.equals(array[i]))) return false; else newArray[i] = array[i];
        }
        newArray[len] = element;
        array = newArray;
        return true;
    }
    
    public boolean containsAll(Collection c) {
        Object[] elementData = array();
        int len = elementData.length;
        Iterator e = c.iterator();
        while (e.hasNext()) if (indexOf(e.next(), elementData, len) < 0) return false;
        return true;
    }
    
    public synchronized boolean removeAll(Collection c) {
        Object[] elementData = array;
        int len = elementData.length;
        if (len == 0) return false;
        Object[] temp = (Object[])new Object[len];
        int newlen = 0;
        for (int i = 0; i < len; ++i) {
            Object element = elementData[i];
            if (!c.contains(element)) {
                temp[newlen++] = element;
            }
        }
        if (newlen == len) return false;
        Object[] newArray = (Object[])new Object[newlen];
        System.arraycopy(temp, 0, newArray, 0, newlen);
        array = newArray;
        return true;
    }
    
    public synchronized boolean retainAll(Collection c) {
        Object[] elementData = array;
        int len = elementData.length;
        if (len == 0) return false;
        Object[] temp = (Object[])new Object[len];
        int newlen = 0;
        for (int i = 0; i < len; ++i) {
            Object element = elementData[i];
            if (c.contains(element)) {
                temp[newlen++] = element;
            }
        }
        if (newlen == len) return false;
        Object[] newArray = (Object[])new Object[newlen];
        System.arraycopy(temp, 0, newArray, 0, newlen);
        array = newArray;
        return true;
    }
    
    public synchronized int addAllAbsent(Collection c) {
        int numNew = c.size();
        if (numNew == 0) return 0;
        Object[] elementData = array;
        int len = elementData.length;
        Object[] temp = (Object[])new Object[numNew];
        int added = 0;
        Iterator e = c.iterator();
        while (e.hasNext()) {
            Object element = e.next();
            if (indexOf(element, elementData, len) < 0) {
                if (indexOf(element, temp, added) < 0) {
                    temp[added++] = element;
                }
            }
        }
        if (added == 0) return 0;
        Object[] newArray = (Object[])new Object[len + added];
        System.arraycopy(elementData, 0, newArray, 0, len);
        System.arraycopy(temp, 0, newArray, len, added);
        array = newArray;
        return added;
    }
    
    public synchronized void clear() {
        array = (Object[])new Object[0];
    }
    
    public synchronized boolean addAll(Collection c) {
        int numNew = c.size();
        if (numNew == 0) return false;
        int len = array.length;
        Object[] newArray = (Object[])new Object[len + numNew];
        System.arraycopy(array, 0, newArray, 0, len);
        Iterator e = c.iterator();
        for (int i = 0; i < numNew; i++) newArray[len++] = e.next();
        array = newArray;
        return true;
    }
    
    public synchronized boolean addAll(int index, Collection c) {
        int len = array.length;
        if (index > len || index < 0) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + len);
        int numNew = c.size();
        if (numNew == 0) return false;
        Object[] newArray = (Object[])new Object[len + numNew];
        System.arraycopy(array, 0, newArray, 0, len);
        int numMoved = len - index;
        if (numMoved > 0) System.arraycopy(array, index, newArray, index + numNew, numMoved);
        Iterator e = c.iterator();
        for (int i = 0; i < numNew; i++) newArray[index++] = e.next();
        array = newArray;
        return true;
    }
    
    private void rangeCheck(int index, int length) {
        if (index >= length || index < 0) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + length);
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        s.defaultWriteObject();
        Object[] elementData = array();
        s.writeInt(elementData.length);
        for (int i = 0; i < elementData.length; i++) s.writeObject(elementData[i]);
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        int arrayLength = s.readInt();
        Object[] elementData = (Object[])new Object[arrayLength];
        for (int i = 0; i < elementData.length; i++) elementData[i] = (Object)s.readObject();
        array = elementData;
    }
    
    public String toString() {
        StringBuffer buf = new StringBuffer();
        Iterator e = iterator();
        buf.append("[");
        int maxIndex = size() - 1;
        for (int i = 0; i <= maxIndex; i++) {
            buf.append(String.valueOf(e.next()));
            if (i < maxIndex) buf.append(", ");
        }
        buf.append("]");
        return buf.toString();
    }
    
    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof List)) return false;
        List l2 = (List)((List)o);
        if (size() != l2.size()) return false;
        ListIterator e1 = listIterator();
        ListIterator e2 = l2.listIterator();
        while (e1.hasNext()) {
            Object o1 = e1.next();
            Object o2 = e2.next();
            if (!(o1 == null ? o2 == null : o1.equals(o2))) return false;
        }
        return true;
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
    
    public Iterator iterator() {
        return new CopyOnWriteArrayList$COWIterator(array(), 0, null);
    }
    
    public ListIterator listIterator() {
        return new CopyOnWriteArrayList$COWIterator(array(), 0, null);
    }
    
    public ListIterator listIterator(final int index) {
        Object[] elementData = array();
        int len = elementData.length;
        if (index < 0 || index > len) throw new IndexOutOfBoundsException("Index: " + index);
        return new CopyOnWriteArrayList$COWIterator(array(), index, null);
    }
    {
    }
    
    public synchronized List subList(int fromIndex, int toIndex) {
        int len = array.length;
        if (fromIndex < 0 || toIndex > len || fromIndex > toIndex) throw new IndexOutOfBoundsException();
        return new CopyOnWriteArrayList$COWSubList(this, fromIndex, toIndex, null);
    }
    {
    }
    {
    }
}
