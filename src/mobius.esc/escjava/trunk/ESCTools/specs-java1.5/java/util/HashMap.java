package java.util;

import java.io.*;

public class HashMap extends AbstractMap implements Map, Cloneable, Serializable {
    {
    }
    static final int DEFAULT_INITIAL_CAPACITY = 16;
    static final int MAXIMUM_CAPACITY = 1 << 30;
    static final float DEFAULT_LOAD_FACTOR = 0.75F;
    transient HashMap$Entry[] table;
    transient int size;
    int threshold;
    final float loadFactor;
    volatile transient int modCount;
    
    public HashMap(int initialCapacity, float loadFactor) {
        
        if (initialCapacity < 0) throw new IllegalArgumentException("Illegal initial capacity: " + initialCapacity);
        if (initialCapacity > MAXIMUM_CAPACITY) initialCapacity = MAXIMUM_CAPACITY;
        if (loadFactor <= 0 || Float.isNaN(loadFactor)) throw new IllegalArgumentException("Illegal load factor: " + loadFactor);
        int capacity = 1;
        while (capacity < initialCapacity) capacity <<= 1;
        this.loadFactor = loadFactor;
        threshold = (int)(capacity * loadFactor);
        table = new HashMap$Entry[capacity];
        init();
    }
    
    public HashMap(int initialCapacity) {
        this(initialCapacity, DEFAULT_LOAD_FACTOR);
    }
    
    public HashMap() {
        
        this.loadFactor = DEFAULT_LOAD_FACTOR;
        threshold = (int)(DEFAULT_INITIAL_CAPACITY * DEFAULT_LOAD_FACTOR);
        table = new HashMap$Entry[DEFAULT_INITIAL_CAPACITY];
        init();
    }
    
    public HashMap(Map m) {
        this(Math.max((int)(m.size() / DEFAULT_LOAD_FACTOR) + 1, DEFAULT_INITIAL_CAPACITY), DEFAULT_LOAD_FACTOR);
        putAllForCreate(m);
    }
    
    void init() {
    }
    static final Object NULL_KEY = new Object();
    
    static Object maskNull(Object key) {
        return key == null ? (Object)NULL_KEY : key;
    }
    
    static Object unmaskNull(Object key) {
        return (key == NULL_KEY ? null : key);
    }
    private static final boolean useNewHash;
    static {
        useNewHash = false;
    }
    
    private static int oldHash(int h) {
        h += ~(h << 9);
        h ^= (h >>> 14);
        h += (h << 4);
        h ^= (h >>> 10);
        return h;
    }
    
    private static int newHash(int h) {
        h ^= (h >>> 20) ^ (h >>> 12);
        return h ^ (h >>> 7) ^ (h >>> 4);
    }
    
    static int hash(int h) {
        return useNewHash ? newHash(h) : oldHash(h);
    }
    
    static int hash(Object key) {
        return hash(key.hashCode());
    }
    
    static boolean eq(Object x, Object y) {
        return x == y || x.equals(y);
    }
    
    static int indexFor(int h, int length) {
        return h & (length - 1);
    }
    
    public int size() {
        return size;
    }
    
    public boolean isEmpty() {
        return size == 0;
    }
    
    public Object get(Object key) {
        if (key == null) return getForNullKey();
        int hash = hash(key.hashCode());
        for (HashMap$Entry e = table[indexFor(hash, table.length)]; e != null; e = e.next) {
            Object k;
            if (e.hash == hash && ((k = e.key) == key || key.equals(k))) return e.value;
        }
        return null;
    }
    
    private Object getForNullKey() {
        int hash = hash(NULL_KEY.hashCode());
        int i = indexFor(hash, table.length);
        HashMap$Entry e = table[i];
        while (true) {
            if (e == null) return null;
            if (e.key == NULL_KEY) return e.value;
            e = e.next;
        }
    }
    
    public boolean containsKey(Object key) {
        Object k = maskNull(key);
        int hash = hash(k.hashCode());
        int i = indexFor(hash, table.length);
        HashMap$Entry e = table[i];
        while (e != null) {
            if (e.hash == hash && eq(k, e.key)) return true;
            e = e.next;
        }
        return false;
    }
    
    HashMap$Entry getEntry(Object key) {
        Object k = maskNull(key);
        int hash = hash(k.hashCode());
        int i = indexFor(hash, table.length);
        HashMap$Entry e = table[i];
        while (e != null && !(e.hash == hash && eq(k, e.key))) e = e.next;
        return e;
    }
    
    public Object put(Object key, Object value) {
        if (key == null) return putForNullKey(value);
        int hash = hash(key.hashCode());
        int i = indexFor(hash, table.length);
        for (HashMap$Entry e = table[i]; e != null; e = e.next) {
            Object k;
            if (e.hash == hash && ((k = e.key) == key || key.equals(k))) {
                Object oldValue = e.value;
                e.value = value;
                e.recordAccess(this);
                return oldValue;
            }
        }
        modCount++;
        addEntry(hash, key, value, i);
        return null;
    }
    
    private Object putForNullKey(Object value) {
        int hash = hash(NULL_KEY.hashCode());
        int i = indexFor(hash, table.length);
        for (HashMap$Entry e = table[i]; e != null; e = e.next) {
            if (e.key == NULL_KEY) {
                Object oldValue = e.value;
                e.value = value;
                e.recordAccess(this);
                return oldValue;
            }
        }
        modCount++;
        addEntry(hash, (Object)NULL_KEY, value, i);
        return null;
    }
    
    private void putForCreate(Object key, Object value) {
        Object k = maskNull(key);
        int hash = hash(k.hashCode());
        int i = indexFor(hash, table.length);
        for (HashMap$Entry e = table[i]; e != null; e = e.next) {
            if (e.hash == hash && eq(k, e.key)) {
                e.value = value;
                return;
            }
        }
        createEntry(hash, k, value, i);
    }
    
    void putAllForCreate(Map m) {
        for (Iterator i = m.entrySet().iterator(); i.hasNext(); ) {
            Map$Entry e = (Map$Entry)i.next();
            putForCreate(e.getKey(), e.getValue());
        }
    }
    
    void resize(int newCapacity) {
        HashMap$Entry[] oldTable = table;
        int oldCapacity = oldTable.length;
        if (oldCapacity == MAXIMUM_CAPACITY) {
            threshold = Integer.MAX_VALUE;
            return;
        }
        HashMap$Entry[] newTable = new HashMap$Entry[newCapacity];
        transfer(newTable);
        table = newTable;
        threshold = (int)(newCapacity * loadFactor);
    }
    
    void transfer(HashMap$Entry[] newTable) {
        HashMap$Entry[] src = table;
        int newCapacity = newTable.length;
        for (int j = 0; j < src.length; j++) {
            HashMap$Entry e = src[j];
            if (e != null) {
                src[j] = null;
                do {
                    HashMap$Entry next = e.next;
                    int i = indexFor(e.hash, newCapacity);
                    e.next = newTable[i];
                    newTable[i] = e;
                    e = next;
                }                 while (e != null);
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
        HashMap$Entry e = removeEntryForKey(key);
        return (e == null ? null : e.value);
    }
    
    HashMap$Entry removeEntryForKey(Object key) {
        Object k = maskNull(key);
        int hash = hash(k.hashCode());
        int i = indexFor(hash, table.length);
        HashMap$Entry prev = table[i];
        HashMap$Entry e = prev;
        while (e != null) {
            HashMap$Entry next = e.next;
            if (e.hash == hash && eq(k, e.key)) {
                modCount++;
                size--;
                if (prev == e) table[i] = next; else prev.next = next;
                e.recordRemoval(this);
                return e;
            }
            prev = e;
            e = next;
        }
        return e;
    }
    
    HashMap$Entry removeMapping(Object o) {
        if (!(o instanceof Map$Entry)) return null;
        Map$Entry entry = (Map$Entry)(Map$Entry)o;
        Object k = maskNull(entry.getKey());
        int hash = hash(k.hashCode());
        int i = indexFor(hash, table.length);
        HashMap$Entry prev = table[i];
        HashMap$Entry e = prev;
        while (e != null) {
            HashMap$Entry next = e.next;
            if (e.hash == hash && e.equals(entry)) {
                modCount++;
                size--;
                if (prev == e) table[i] = next; else prev.next = next;
                e.recordRemoval(this);
                return e;
            }
            prev = e;
            e = next;
        }
        return e;
    }
    
    public void clear() {
        modCount++;
        HashMap$Entry[] tab = table;
        for (int i = 0; i < tab.length; i++) tab[i] = null;
        size = 0;
    }
    
    public boolean containsValue(Object value) {
        if (value == null) return containsNullValue();
        HashMap$Entry[] tab = table;
        for (int i = 0; i < tab.length; i++) for (HashMap$Entry e = tab[i]; e != null; e = e.next) if (value.equals(e.value)) return true;
        return false;
    }
    
    private boolean containsNullValue() {
        HashMap$Entry[] tab = table;
        for (int i = 0; i < tab.length; i++) for (HashMap$Entry e = tab[i]; e != null; e = e.next) if (e.value == null) return true;
        return false;
    }
    
    public Object clone() {
        HashMap result = null;
        try {
            result = (HashMap)(HashMap)super.clone();
        } catch (CloneNotSupportedException e) {
        }
        result.table = new HashMap$Entry[table.length];
        result.entrySet = null;
        result.modCount = 0;
        result.size = 0;
        result.init();
        result.putAllForCreate(this);
        return result;
    }
    {
    }
    
    void addEntry(int hash, Object key, Object value, int bucketIndex) {
        HashMap$Entry e = table[bucketIndex];
        table[bucketIndex] = new HashMap$Entry(hash, key, value, e);
        if (size++ >= threshold) resize(2 * table.length);
    }
    
    void createEntry(int hash, Object key, Object value, int bucketIndex) {
        HashMap$Entry e = table[bucketIndex];
        table[bucketIndex] = new HashMap$Entry(hash, key, value, e);
        size++;
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    Iterator newKeyIterator() {
        return new HashMap$KeyIterator(this, null);
    }
    
    Iterator newValueIterator() {
        return new HashMap$ValueIterator(this, null);
    }
    
    Iterator newEntryIterator() {
        return new HashMap$EntryIterator(this, null);
    }
    private transient Set entrySet = null;
    
    public Set keySet() {
        Set ks = keySet;
        return (ks != null ? ks : (keySet = new HashMap$KeySet(this, null)));
    }
    {
    }
    
    public Collection values() {
        Collection vs = values;
        return (vs != null ? vs : (values = new HashMap$Values(this, null)));
    }
    {
    }
    
    public Set entrySet() {
        Set es = entrySet;
        return (es != null ? es : (entrySet = (Set)(Set)new HashMap$EntrySet(this, null)));
    }
    {
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws IOException {
        Iterator i = entrySet().iterator();
        s.defaultWriteObject();
        s.writeInt(table.length);
        s.writeInt(size);
        while (i.hasNext()) {
            Map$Entry e = (Map$Entry)i.next();
            s.writeObject(e.getKey());
            s.writeObject(e.getValue());
        }
    }
    private static final long serialVersionUID = 362498820763181265L;
    
    private void readObject(java.io.ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        int numBuckets = s.readInt();
        table = new HashMap$Entry[numBuckets];
        init();
        int size = s.readInt();
        for (int i = 0; i < size; i++) {
            Object key = (Object)s.readObject();
            Object value = (Object)s.readObject();
            putForCreate(key, value);
        }
    }
    
    int capacity() {
        return table.length;
    }
    
    float loadFactor() {
        return loadFactor;
    }
}
