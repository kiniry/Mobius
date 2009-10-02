package java.util;

import java.lang.reflect.Array;

class Collections$CheckedMap$CheckedEntrySet implements Set {
    Set s;
    Class valueType;
    
    Collections$CheckedMap$CheckedEntrySet(Set s, Class valueType) {
        
        this.s = s;
        this.valueType = valueType;
    }
    
    public int size() {
        return s.size();
    }
    
    public boolean isEmpty() {
        return s.isEmpty();
    }
    
    public String toString() {
        return s.toString();
    }
    
    public int hashCode() {
        return s.hashCode();
    }
    
    public boolean remove(Object o) {
        return s.remove(o);
    }
    
    public boolean removeAll(Collection coll) {
        return s.removeAll(coll);
    }
    
    public boolean retainAll(Collection coll) {
        return s.retainAll(coll);
    }
    
    public void clear() {
        s.clear();
    }
    
    public boolean add(Map$Entry o) {
        throw new UnsupportedOperationException();
    }
    
    public boolean addAll(Collection coll) {
        throw new UnsupportedOperationException();
    }
    
    public Iterator iterator() {
        return new Collections$CheckedMap$CheckedEntrySet$1(this);
    }
    
    public Object[] toArray() {
        Object[] source = s.toArray();
        Object[] dest = (Collections.CheckedMap.CheckedEntrySet.CheckedEntry.class.isInstance(source.getClass().getComponentType()) ? source : new Object[source.length]);
        for (int i = 0; i < source.length; i++) dest[i] = new Collections$CheckedMap$CheckedEntrySet$CheckedEntry((Map$Entry)(Map$Entry)source[i], valueType);
        return dest;
    }
    
    public Object[] toArray(Object[] a) {
        Object[] arr = s.toArray(a.length == 0 ? a : (Object[])(Object[])Array.newInstance(a.getClass().getComponentType(), 0));
        for (int i = 0; i < arr.length; i++) arr[i] = new Collections$CheckedMap$CheckedEntrySet$CheckedEntry((Map$Entry)(Map$Entry)arr[i], valueType);
        if (arr.length > a.length) return (Object[])arr;
        System.arraycopy(arr, 0, a, 0, arr.length);
        if (a.length > arr.length) a[arr.length] = null;
        return a;
    }
    
    public boolean contains(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        return s.contains(new Collections$CheckedMap$CheckedEntrySet$CheckedEntry((Map$Entry)(Map$Entry)o, valueType));
    }
    
    public boolean containsAll(Collection coll) {
        Iterator e = coll.iterator();
        while (e.hasNext()) if (!contains(e.next())) return false;
        return true;
    }
    
    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof Set)) return false;
        Set that = (Set)(Set)o;
        if (that.size() != s.size()) return false;
        return containsAll(that);
    }
    {
    }
    
    /*synthetic*/ public boolean add(Object x0) {
        return this.add((Map$Entry)x0);
    }
}
