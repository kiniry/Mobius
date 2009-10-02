package java.util;

import java.lang.ref.ReferenceQueue;

public class WeakHashMap extends AbstractMap implements Map {
    
    /*synthetic*/ static WeakHashMap.Entry[] access$500(WeakHashMap x0) {
        return x0.table;
    }
    
    /*synthetic*/ static int access$400(WeakHashMap x0) {
        return x0.modCount;
    }
    
    /*synthetic*/ static Object access$300(Object x0) {
        return unmaskNull(x0);
    }
    {
    }
    private static final int DEFAULT_INITIAL_CAPACITY = 16;
    private static final int MAXIMUM_CAPACITY = 1 << 30;
    private static final float DEFAULT_LOAD_FACTOR = 0.75F;
    private WeakHashMap$Entry[] table;
    private int size;
    private int threshold;
    private final float loadFactor;
    private final ReferenceQueue queue = new ReferenceQueue();
    private volatile int modCount;
    
    public WeakHashMap(int initialCapacity, float loadFactor) {
        
        if (initialCapacity < 0) throw new IllegalArgumentException("Illegal Initial Capacity: " + initialCapacity);
        if (initialCapacity > MAXIMUM_CAPACITY) initialCapacity = MAXIMUM_CAPACITY;
        if (loadFactor <= 0 || Float.isNaN(loadFactor)) throw new IllegalArgumentException("Illegal Load factor: " + loadFactor);
        int capacity = 1;
        while (capacity < initialCapacity) capacity <<= 1;
        table = new WeakHashMap$Entry[capacity];
        this.loadFactor = loadFactor;
        threshold = (int)(capacity * loadFactor);
    }
    
    public WeakHashMap(int initialCapacity) {
        this(initialCapacity, DEFAULT_LOAD_FACTOR);
    }
    
    public WeakHashMap() {
        
        this.loadFactor = DEFAULT_LOAD_FACTOR;
        threshold = (int)(DEFAULT_INITIAL_CAPACITY);
        table = new WeakHashMap$Entry[DEFAULT_INITIAL_CAPACITY];
    }
    
    public WeakHashMap(Map t) {
        this(Math.max((int)(t.size() / DEFAULT_LOAD_FACTOR) + 1, 16), DEFAULT_LOAD_FACTOR);
        putAll(t);
    }
    private static final Object NULL_KEY = new Object();
    
    private static Object maskNull(Object key) {
        return (key == null ? NULL_KEY : key);
    }
    
    private static Object unmaskNull(Object key) {
        return (Object)(key == NULL_KEY ? null : key);
    }
    
    static boolean eq(Object x, Object y) {
        return x == y || x.equals(y);
    }
    
    static int indexFor(int h, int length) {
        return h & (length - 1);
    }
    
    private void expungeStaleEntries() {
        WeakHashMap$Entry e;
        while ((e = (WeakHashMap$Entry)(WeakHashMap$Entry)queue.poll()) != null) {
            int h = WeakHashMap.Entry.access$000(e);
            int i = indexFor(h, table.length);
            WeakHashMap$Entry prev = table[i];
            WeakHashMap$Entry p = prev;
            while (p != null) {
                WeakHashMap$Entry next = WeakHashMap.Entry.access$100(p);
                if (p == e) {
                    if (prev == e) table[i] = next; else WeakHashMap.Entry.access$102(prev, next);
                    WeakHashMap.Entry.access$102(e, null);
                    WeakHashMap.Entry.access$202(e, null);
                    size--;
                    break;
                }
                prev = p;
                p = next;
            }
        }
    }
    
    private WeakHashMap$Entry[] getTable() {
        expungeStaleEntries();
        return table;
    }
    
    public int size() {
        if (size == 0) return 0;
        expungeStaleEntries();
        return size;
    }
    
    public boolean isEmpty() {
        return size() == 0;
    }
    
    public Object get(Object key) {
        Object k = maskNull(key);
        int h = HashMap.hash(k);
        WeakHashMap$Entry[] tab = getTable();
        int index = indexFor(h, tab.length);
        WeakHashMap$Entry e = tab[index];
        while (e != null) {
            if (WeakHashMap.Entry.access$000(e) == h && eq(k, e.get())) return WeakHashMap.Entry.access$200(e);
            e = WeakHashMap.Entry.access$100(e);
        }
        return null;
    }
    
    public boolean containsKey(Object key) {
        return getEntry(key) != null;
    }
    
    WeakHashMap$Entry getEntry(Object key) {
        Object k = maskNull(key);
        int h = HashMap.hash(k);
        WeakHashMap$Entry[] tab = getTable();
        int index = indexFor(h, tab.length);
        WeakHashMap$Entry e = tab[index];
        while (e != null && !(WeakHashMap.Entry.access$000(e) == h && eq(k, e.get()))) e = WeakHashMap.Entry.access$100(e);
        return e;
    }
    
    public Object put(Object key, Object value) {
        Object k = (Object)maskNull(key);
        int h = HashMap.hash(k);
        WeakHashMap$Entry[] tab = getTable();
        int i = indexFor(h, tab.length);
        for (WeakHashMap$Entry e = tab[i]; e != null; e = WeakHashMap.Entry.access$100(e)) {
            if (h == WeakHashMap.Entry.access$000(e) && eq(k, e.get())) {
                Object oldValue = WeakHashMap.Entry.access$200(e);
                if (value != oldValue) WeakHashMap.Entry.access$202(e, value);
                return oldValue;
            }
        }
        modCount++;
        WeakHashMap$Entry e = tab[i];
        tab[i] = new WeakHashMap$Entry(k, value, queue, h, e);
        if (++size >= threshold) resize(tab.length * 2);
        return null;
    }
    
    void resize(int newCapacity) {
        WeakHashMap$Entry[] oldTable = getTable();
        int oldCapacity = oldTable.length;
        if (oldCapacity == MAXIMUM_CAPACITY) {
            threshold = Integer.MAX_VALUE;
            return;
        }
        WeakHashMap$Entry[] newTable = new WeakHashMap$Entry[newCapacity];
        transfer(oldTable, newTable);
        table = newTable;
        if (size >= threshold / 2) {
            threshold = (int)(newCapacity * loadFactor);
        } else {
            expungeStaleEntries();
            transfer(newTable, oldTable);
            table = oldTable;
        }
    }
    
    private void transfer(WeakHashMap$Entry[] src, WeakHashMap$Entry[] dest) {
        for (int j = 0; j < src.length; ++j) {
            WeakHashMap$Entry e = src[j];
            src[j] = null;
            while (e != null) {
                WeakHashMap$Entry next = WeakHashMap.Entry.access$100(e);
                Object key = e.get();
                if (key == null) {
                    WeakHashMap.Entry.access$102(e, null);
                    WeakHashMap.Entry.access$202(e, null);
                    size--;
                } else {
                    int i = indexFor(WeakHashMap.Entry.access$000(e), dest.length);
                    WeakHashMap.Entry.access$102(e, dest[i]);
                    dest[i] = e;
                }
                e = next;
            }
        }
    }
    
    public void putAll(Map m) {
        int numKeysToBeAdded = m.size();
        if (numKeysToBeAdded == 0) return;
        if (numKeysToBeAdded > threshold) {
            int targetCapacity = (int)(numKeysToBeAdded / loadFactor + 1);
            if (targetCapacity > MAXIMUM_CAPACITY) targetCapacity = MAXIMUM_CAPACITY;
            int newCapacity = table.length;
            while (newCapacity < targetCapacity) newCapacity <<= 1;
            if (newCapacity > table.length) resize(newCapacity);
        }
        for (Iterator i = m.entrySet().iterator(); i.hasNext(); ) {
            Map$Entry e = (Map$Entry)i.next();
            put(e.getKey(), e.getValue());
        }
    }
    
    public Object remove(Object key) {
        Object k = maskNull(key);
        int h = HashMap.hash(k);
        WeakHashMap$Entry[] tab = getTable();
        int i = indexFor(h, tab.length);
        WeakHashMap$Entry prev = tab[i];
        WeakHashMap$Entry e = prev;
        while (e != null) {
            WeakHashMap$Entry next = WeakHashMap.Entry.access$100(e);
            if (h == WeakHashMap.Entry.access$000(e) && eq(k, e.get())) {
                modCount++;
                size--;
                if (prev == e) tab[i] = next; else WeakHashMap.Entry.access$102(prev, next);
                return WeakHashMap.Entry.access$200(e);
            }
            prev = e;
            e = next;
        }
        return null;
    }
    
    WeakHashMap$Entry removeMapping(Object o) {
        if (!(o instanceof Map$Entry)) return null;
        WeakHashMap$Entry[] tab = getTable();
        Map$Entry entry = (Map$Entry)(Map$Entry)o;
        Object k = maskNull(entry.getKey());
        int h = HashMap.hash(k);
        int i = indexFor(h, tab.length);
        WeakHashMap$Entry prev = tab[i];
        WeakHashMap$Entry e = prev;
        while (e != null) {
            WeakHashMap$Entry next = WeakHashMap.Entry.access$100(e);
            if (h == WeakHashMap.Entry.access$000(e) && e.equals(entry)) {
                modCount++;
                size--;
                if (prev == e) tab[i] = next; else WeakHashMap.Entry.access$102(prev, next);
                return e;
            }
            prev = e;
            e = next;
        }
        return null;
    }
    
    public void clear() {
        while (queue.poll() != null) ;
        modCount++;
        WeakHashMap$Entry[] tab = table;
        for (int i = 0; i < tab.length; ++i) tab[i] = null;
        size = 0;
        while (queue.poll() != null) ;
    }
    
    public boolean containsValue(Object value) {
        if (value == null) return containsNullValue();
        WeakHashMap$Entry[] tab = getTable();
        for (int i = tab.length; i-- > 0; ) for (WeakHashMap$Entry e = tab[i]; e != null; e = WeakHashMap.Entry.access$100(e)) if (value.equals(WeakHashMap.Entry.access$200(e))) return true;
        return false;
    }
    
    private boolean containsNullValue() {
        WeakHashMap$Entry[] tab = getTable();
        for (int i = tab.length; i-- > 0; ) for (WeakHashMap$Entry e = tab[i]; e != null; e = WeakHashMap.Entry.access$100(e)) if (WeakHashMap.Entry.access$200(e) == null) return true;
        return false;
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    private transient Set entrySet = null;
    
    public Set keySet() {
        Set ks = keySet;
        return (ks != null ? ks : (keySet = new WeakHashMap$KeySet(this, null)));
    }
    {
    }
    
    public Collection values() {
        Collection vs = values;
        return (vs != null ? vs : (values = new WeakHashMap$Values(this, null)));
    }
    {
    }
    
    public Set entrySet() {
        Set es = entrySet;
        return (es != null ? es : (entrySet = new WeakHashMap$EntrySet(this, null)));
    }
    {
    }
}
