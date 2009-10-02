package java.util;

class TreeMap$1 extends AbstractSet {
    /*synthetic*/ final TreeMap this$0;
    
    TreeMap$1(/*synthetic*/ final TreeMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new TreeMap$KeyIterator(this$0, null);
    }
    
    public int size() {
        return this$0.size();
    }
    
    public boolean contains(Object o) {
        return this$0.containsKey(o);
    }
    
    public boolean remove(Object o) {
        int oldSize = TreeMap.access$100(this$0);
        this$0.remove(o);
        return TreeMap.access$100(this$0) != oldSize;
    }
    
    public void clear() {
        this$0.clear();
    }
}
