package java.util;

class TreeMap$2 extends AbstractCollection {
    /*synthetic*/ final TreeMap this$0;
    
    TreeMap$2(/*synthetic*/ final TreeMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new TreeMap$ValueIterator(this$0, null);
    }
    
    public int size() {
        return this$0.size();
    }
    
    public boolean contains(Object o) {
        for (TreeMap$Entry e = TreeMap.access$300(this$0); e != null; e = TreeMap.access$400(this$0, e)) if (TreeMap.access$500(e.getValue(), o)) return true;
        return false;
    }
    
    public boolean remove(Object o) {
        for (TreeMap$Entry e = TreeMap.access$300(this$0); e != null; e = TreeMap.access$400(this$0, e)) {
            if (TreeMap.access$500(e.getValue(), o)) {
                TreeMap.access$600(this$0, e);
                return true;
            }
        }
        return false;
    }
    
    public void clear() {
        this$0.clear();
    }
}
