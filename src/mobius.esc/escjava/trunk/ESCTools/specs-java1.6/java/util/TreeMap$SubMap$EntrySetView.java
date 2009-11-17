package java.util;

class TreeMap$SubMap$EntrySetView extends AbstractSet {
    
    /*synthetic*/ TreeMap$SubMap$EntrySetView(TreeMap.SubMap x0, java.util.TreeMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final TreeMap$SubMap this$1;
    
    private TreeMap$SubMap$EntrySetView(/*synthetic*/ final TreeMap$SubMap this$1) {
        this.this$1 = this$1;
        
    }
    private transient int size = -1;
    private transient int sizeModCount;
    
    public int size() {
        if (size == -1 || sizeModCount != TreeMap.access$1600(this$1.this$0)) {
            size = 0;
            sizeModCount = TreeMap.access$1600(this$1.this$0);
            Iterator i = iterator();
            while (i.hasNext()) {
                size++;
                i.next();
            }
        }
        return size;
    }
    
    public boolean isEmpty() {
        return !iterator().hasNext();
    }
    
    public boolean contains(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry entry = (Map$Entry)(Map$Entry)o;
        Object key = entry.getKey();
        if (!TreeMap.SubMap.access$1700(this$1, key)) return false;
        TreeMap$Entry node = TreeMap.access$800(this$1.this$0, key);
        return node != null && TreeMap.access$500(node.getValue(), entry.getValue());
    }
    
    public boolean remove(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry entry = (Map$Entry)(Map$Entry)o;
        Object key = entry.getKey();
        if (!TreeMap.SubMap.access$1700(this$1, key)) return false;
        TreeMap$Entry node = TreeMap.access$800(this$1.this$0, key);
        if (node != null && TreeMap.access$500(node.getValue(), entry.getValue())) {
            TreeMap.access$600(this$1.this$0, node);
            return true;
        }
        return false;
    }
    
    public Iterator iterator() {
        return new TreeMap$SubMapEntryIterator(this$1.this$0, (TreeMap.SubMap.access$1800(this$1) ? TreeMap.access$300(this$1.this$0) : TreeMap.access$1100(this$1.this$0, TreeMap.SubMap.access$1900(this$1))), (TreeMap.SubMap.access$2000(this$1) ? null : TreeMap.access$1100(this$1.this$0, TreeMap.SubMap.access$2100(this$1))));
    }
}
