package java.util;

import java.io.*;

public class LinkedHashMap extends HashMap implements Map {
    
    /*synthetic*/ static LinkedHashMap$Entry access$100(LinkedHashMap x0) {
        return x0.header;
    }
    
    /*synthetic*/ static boolean access$000(LinkedHashMap x0) {
        return x0.accessOrder;
    }
    {
    }
    private static final long serialVersionUID = 3801124242820219131L;
    private transient LinkedHashMap$Entry header;
    private final boolean accessOrder;
    
    public LinkedHashMap(int initialCapacity, float loadFactor) {
        super(initialCapacity, loadFactor);
        accessOrder = false;
    }
    
    public LinkedHashMap(int initialCapacity) {
        super(initialCapacity);
        accessOrder = false;
    }
    
    public LinkedHashMap() {
        
        accessOrder = false;
    }
    
    public LinkedHashMap(Map m) {
        super(m);
        accessOrder = false;
    }
    
    public LinkedHashMap(int initialCapacity, float loadFactor, boolean accessOrder) {
        super(initialCapacity, loadFactor);
        this.accessOrder = accessOrder;
    }
    
    void init() {
        header = new LinkedHashMap$Entry(-1, null, null, null);
        header.before = header.after = header;
    }
    
    void transfer(HashMap$Entry[] newTable) {
        int newCapacity = newTable.length;
        for (LinkedHashMap$Entry e = header.after; e != header; e = e.after) {
            int index = indexFor(e.hash, newCapacity);
            e.next = newTable[index];
            newTable[index] = e;
        }
    }
    
    public boolean containsValue(Object value) {
        if (value == null) {
            for (LinkedHashMap$Entry e = header.after; e != header; e = e.after) if (e.value == null) return true;
        } else {
            for (LinkedHashMap$Entry e = header.after; e != header; e = e.after) if (value.equals(e.value)) return true;
        }
        return false;
    }
    
    public Object get(Object key) {
        LinkedHashMap$Entry e = (LinkedHashMap$Entry)(LinkedHashMap$Entry)getEntry(key);
        if (e == null) return null;
        e.recordAccess(this);
        return e.value;
    }
    
    public void clear() {
        super.clear();
        header.before = header.after = header;
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
    
    Iterator newKeyIterator() {
        return new LinkedHashMap$KeyIterator(this, null);
    }
    
    Iterator newValueIterator() {
        return new LinkedHashMap$ValueIterator(this, null);
    }
    
    Iterator newEntryIterator() {
        return new LinkedHashMap$EntryIterator(this, null);
    }
    
    void addEntry(int hash, Object key, Object value, int bucketIndex) {
        createEntry(hash, key, value, bucketIndex);
        LinkedHashMap$Entry eldest = header.after;
        if (removeEldestEntry(eldest)) {
            removeEntryForKey(eldest.key);
        } else {
            if (size >= threshold) resize(2 * table.length);
        }
    }
    
    void createEntry(int hash, Object key, Object value, int bucketIndex) {
        HashMap$Entry old = table[bucketIndex];
        LinkedHashMap$Entry e = new LinkedHashMap$Entry(hash, key, value, old);
        table[bucketIndex] = e;
        LinkedHashMap.Entry.access$600(e, header);
        size++;
    }
    
    protected boolean removeEldestEntry(Map$Entry eldest) {
        return false;
    }
}
