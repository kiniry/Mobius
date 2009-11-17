package java.util;

class WeakHashMap$EntrySet extends AbstractSet {
    
    /*synthetic*/ WeakHashMap$EntrySet(WeakHashMap x0, java.util.WeakHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final WeakHashMap this$0;
    
    private WeakHashMap$EntrySet(/*synthetic*/ final WeakHashMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new WeakHashMap$EntryIterator(this$0, null);
    }
    
    public boolean contains(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry e = (Map$Entry)(Map$Entry)o;
        Object k = e.getKey();
        WeakHashMap$Entry candidate = this$0.getEntry(e.getKey());
        return candidate != null && candidate.equals(e);
    }
    
    public boolean remove(Object o) {
        return this$0.removeMapping(o) != null;
    }
    
    public int size() {
        return this$0.size();
    }
    
    public void clear() {
        this$0.clear();
    }
    
    public Object[] toArray() {
        Collection c = new ArrayList(size());
        for (Iterator i = iterator(); i.hasNext(); ) c.add(new AbstractMap$SimpleEntry((Map$Entry)i.next()));
        return c.toArray();
    }
    
    public Object[] toArray(Object[] a) {
        Collection c = new ArrayList(size());
        for (Iterator i = iterator(); i.hasNext(); ) c.add(new AbstractMap$SimpleEntry((Map$Entry)i.next()));
        return c.toArray(a);
    }
}
