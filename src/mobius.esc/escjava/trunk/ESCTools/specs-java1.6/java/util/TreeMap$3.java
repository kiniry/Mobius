package java.util;

class TreeMap$3 extends AbstractSet {
    /*synthetic*/ final TreeMap this$0;
    
    TreeMap$3(/*synthetic*/ final TreeMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new TreeMap$EntryIterator(this$0, null);
    }
    
    public boolean contains(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry entry = (Map$Entry)(Map$Entry)o;
        Object value = entry.getValue();
        TreeMap$Entry p = TreeMap.access$800(this$0, entry.getKey());
        return p != null && TreeMap.access$500(p.getValue(), value);
    }
    
    public boolean remove(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry entry = (Map$Entry)(Map$Entry)o;
        Object value = entry.getValue();
        TreeMap$Entry p = TreeMap.access$800(this$0, entry.getKey());
        if (p != null && TreeMap.access$500(p.getValue(), value)) {
            TreeMap.access$600(this$0, p);
            return true;
        }
        return false;
    }
    
    public int size() {
        return this$0.size();
    }
    
    public void clear() {
        this$0.clear();
    }
}
