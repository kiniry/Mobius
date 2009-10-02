package java.util;

class WeakHashMap$KeySet extends AbstractSet {
    
    /*synthetic*/ WeakHashMap$KeySet(WeakHashMap x0, java.util.WeakHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final WeakHashMap this$0;
    
    private WeakHashMap$KeySet(/*synthetic*/ final WeakHashMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new WeakHashMap$KeyIterator(this$0, null);
    }
    
    public int size() {
        return this$0.size();
    }
    
    public boolean contains(Object o) {
        return this$0.containsKey(o);
    }
    
    public boolean remove(Object o) {
        if (this$0.containsKey(o)) {
            this$0.remove(o);
            return true;
        } else return false;
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
