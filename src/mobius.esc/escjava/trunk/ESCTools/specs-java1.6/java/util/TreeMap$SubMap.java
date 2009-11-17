package java.util;

class TreeMap$SubMap extends AbstractMap implements SortedMap, java.io.Serializable {
    
    /*synthetic*/ static Object access$2100(TreeMap$SubMap x0) {
        return x0.toKey;
    }
    
    /*synthetic*/ static boolean access$2000(TreeMap$SubMap x0) {
        return x0.toEnd;
    }
    
    /*synthetic*/ static Object access$1900(TreeMap$SubMap x0) {
        return x0.fromKey;
    }
    
    /*synthetic*/ static boolean access$1800(TreeMap$SubMap x0) {
        return x0.fromStart;
    }
    
    /*synthetic*/ static boolean access$1700(TreeMap$SubMap x0, Object x1) {
        return x0.inRange(x1);
    }
    /*synthetic*/ final TreeMap this$0;
    private static final long serialVersionUID = -6520786458950516097L;
    private boolean fromStart = false;
    private boolean toEnd = false;
    private Object fromKey;
    private Object toKey;
    
    TreeMap$SubMap(/*synthetic*/ final TreeMap this$0, Object fromKey, Object toKey) {
        this.this$0 = this$0;
        
        if (TreeMap.access$900(this$0, fromKey, toKey) > 0) throw new IllegalArgumentException("fromKey > toKey");
        this.fromKey = fromKey;
        this.toKey = toKey;
    }
    
    TreeMap$SubMap(/*synthetic*/ final TreeMap this$0, Object key, boolean headMap) {
        this.this$0 = this$0;
        
        TreeMap.access$900(this$0, key, key);
        if (headMap) {
            fromStart = true;
            toKey = key;
        } else {
            toEnd = true;
            fromKey = key;
        }
    }
    
    TreeMap$SubMap(/*synthetic*/ final TreeMap this$0, boolean fromStart, Object fromKey, boolean toEnd, Object toKey) {
        this.this$0 = this$0;
        
        this.fromStart = fromStart;
        this.fromKey = fromKey;
        this.toEnd = toEnd;
        this.toKey = toKey;
    }
    
    public boolean isEmpty() {
        return entrySet.isEmpty();
    }
    
    public boolean containsKey(Object key) {
        return inRange((Object)key) && this$0.containsKey(key);
    }
    
    public Object get(Object key) {
        if (!inRange((Object)key)) return null;
        return this$0.get(key);
    }
    
    public Object put(Object key, Object value) {
        if (!inRange(key)) throw new IllegalArgumentException("key out of range");
        return this$0.put(key, value);
    }
    
    public Comparator comparator() {
        return TreeMap.access$1000(this$0);
    }
    
    public Object firstKey() {
        TreeMap$Entry e = fromStart ? TreeMap.access$300(this$0) : TreeMap.access$1100(this$0, fromKey);
        Object first = TreeMap.access$1200(e);
        if (!toEnd && TreeMap.access$900(this$0, first, toKey) >= 0) throw (new NoSuchElementException());
        return first;
    }
    
    public Object lastKey() {
        TreeMap$Entry e = toEnd ? TreeMap.access$1300(this$0) : TreeMap.access$1400(this$0, toKey);
        Object last = TreeMap.access$1200(e);
        if (!fromStart && TreeMap.access$900(this$0, last, fromKey) < 0) throw (new NoSuchElementException());
        return last;
    }
    private transient Set entrySet = new TreeMap$SubMap$EntrySetView(this, null);
    
    public Set entrySet() {
        return entrySet;
    }
    {
    }
    
    public SortedMap subMap(Object fromKey, Object toKey) {
        if (!inRange2(fromKey)) throw new IllegalArgumentException("fromKey out of range");
        if (!inRange2(toKey)) throw new IllegalArgumentException("toKey out of range");
        return new TreeMap$SubMap(this$0, fromKey, toKey);
    }
    
    public SortedMap headMap(Object toKey) {
        if (!inRange2(toKey)) throw new IllegalArgumentException("toKey out of range");
        return new TreeMap$SubMap(this$0, fromStart, fromKey, false, toKey);
    }
    
    public SortedMap tailMap(Object fromKey) {
        if (!inRange2(fromKey)) throw new IllegalArgumentException("fromKey out of range");
        return new TreeMap$SubMap(this$0, false, fromKey, toEnd, toKey);
    }
    
    private boolean inRange(Object key) {
        return (fromStart || TreeMap.access$900(this$0, key, fromKey) >= 0) && (toEnd || TreeMap.access$900(this$0, key, toKey) < 0);
    }
    
    private boolean inRange2(Object key) {
        return (fromStart || TreeMap.access$900(this$0, key, fromKey) >= 0) && (toEnd || TreeMap.access$900(this$0, key, toKey) <= 0);
    }
}
