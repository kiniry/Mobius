package java.util;

class Collections$UnmodifiableMap$UnmodifiableEntrySet extends Collections$UnmodifiableSet {
    private static final long serialVersionUID = 7854390611657943733L;
    
    Collections$UnmodifiableMap$UnmodifiableEntrySet(Set s) {
        super((Set)(Set)s);
    }
    
    public Iterator iterator() {
        return new Collections$UnmodifiableMap$UnmodifiableEntrySet$1(this);
    }
    
    public Object[] toArray() {
        Object[] a = c.toArray();
        for (int i = 0; i < a.length; i++) a[i] = new Collections$UnmodifiableMap$UnmodifiableEntrySet$UnmodifiableEntry((Map$Entry)(Map$Entry)a[i]);
        return a;
    }
    
    public Object[] toArray(Object[] a) {
        Object[] arr = c.toArray(a.length == 0 ? a : (Object[])(Object[])java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), 0));
        for (int i = 0; i < arr.length; i++) arr[i] = new Collections$UnmodifiableMap$UnmodifiableEntrySet$UnmodifiableEntry((Map$Entry)(Map$Entry)arr[i]);
        if (arr.length > a.length) return (Object[])arr;
        System.arraycopy(arr, 0, a, 0, arr.length);
        if (a.length > arr.length) a[arr.length] = null;
        return a;
    }
    
    public boolean contains(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        return c.contains(new Collections$UnmodifiableMap$UnmodifiableEntrySet$UnmodifiableEntry((Map$Entry)(Map$Entry)o));
    }
    
    public boolean containsAll(Collection coll) {
        Iterator e = coll.iterator();
        while (e.hasNext()) if (!contains(e.next())) return false;
        return true;
    }
    
    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof Set)) return false;
        Set s = (Set)(Set)o;
        if (s.size() != c.size()) return false;
        return containsAll(s);
    }
    {
    }
}
