package java.util;

class WeakHashMap$Values extends AbstractCollection {
    
    /*synthetic*/ WeakHashMap$Values(WeakHashMap x0, java.util.WeakHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final WeakHashMap this$0;
    
    private WeakHashMap$Values(/*synthetic*/ final WeakHashMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new WeakHashMap$ValueIterator(this$0, null);
    }
    
    public int size() {
        return this$0.size();
    }
    
    public boolean contains(Object o) {
        return this$0.containsValue(o);
    }
    
    public void clear() {
        this$0.clear();
    }
    
    public Object[] toArray() {
        Collection c = new ArrayList(size());
        for (Iterator i = iterator(); i.hasNext(); ) c.add(i.next());
        return c.toArray();
    }
    
    public Object[] toArray(Object[] a) {
        Collection c = new ArrayList(size());
        for (Iterator i = iterator(); i.hasNext(); ) c.add(i.next());
        return c.toArray(a);
    }
}
