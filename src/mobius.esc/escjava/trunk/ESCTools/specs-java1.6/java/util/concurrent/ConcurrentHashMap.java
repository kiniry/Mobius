package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;
import java.io.Serializable;
import java.io.IOException;

public class ConcurrentHashMap extends AbstractMap implements ConcurrentMap, Serializable {
    private static final long serialVersionUID = 7249069246763182397L;
    static int DEFAULT_INITIAL_CAPACITY = 16;
    static final int MAXIMUM_CAPACITY = 1 << 30;
    static final float DEFAULT_LOAD_FACTOR = 0.75F;
    static final int DEFAULT_SEGMENTS = 16;
    static final int MAX_SEGMENTS = 1 << 16;
    static final int RETRIES_BEFORE_LOCK = 2;
    final int segmentMask;
    final int segmentShift;
    final ConcurrentHashMap$Segment[] segments;
    transient Set keySet;
    transient Set entrySet;
    transient Collection values;
    
    static int hash(Object x) {
        int h = x.hashCode();
        h += ~(h << 9);
        h ^= (h >>> 14);
        h += (h << 4);
        h ^= (h >>> 10);
        return h;
    }
    
    final ConcurrentHashMap$Segment segmentFor(int hash) {
        return (ConcurrentHashMap$Segment)segments[(hash >>> segmentShift) & segmentMask];
    }
    {
    }
    {
    }
    
    public ConcurrentHashMap(int initialCapacity, float loadFactor, int concurrencyLevel) {
        
        if (!(loadFactor > 0) || initialCapacity < 0 || concurrencyLevel <= 0) throw new IllegalArgumentException();
        if (concurrencyLevel > MAX_SEGMENTS) concurrencyLevel = MAX_SEGMENTS;
        int sshift = 0;
        int ssize = 1;
        while (ssize < concurrencyLevel) {
            ++sshift;
            ssize <<= 1;
        }
        segmentShift = 32 - sshift;
        segmentMask = ssize - 1;
        this.segments = new ConcurrentHashMap$Segment[ssize];
        if (initialCapacity > MAXIMUM_CAPACITY) initialCapacity = MAXIMUM_CAPACITY;
        int c = initialCapacity / ssize;
        if (c * ssize < initialCapacity) ++c;
        int cap = 1;
        while (cap < c) cap <<= 1;
        for (int i = 0; i < this.segments.length; ++i) this.segments[i] = new ConcurrentHashMap$Segment(cap, loadFactor);
    }
    
    public ConcurrentHashMap(int initialCapacity) {
        this(initialCapacity, DEFAULT_LOAD_FACTOR, DEFAULT_SEGMENTS);
    }
    
    public ConcurrentHashMap() {
        this(DEFAULT_INITIAL_CAPACITY, DEFAULT_LOAD_FACTOR, DEFAULT_SEGMENTS);
    }
    
    public ConcurrentHashMap(Map t) {
        this(Math.max((int)(t.size() / DEFAULT_LOAD_FACTOR) + 1, 11), DEFAULT_LOAD_FACTOR, DEFAULT_SEGMENTS);
        putAll(t);
    }
    
    public boolean isEmpty() {
        final ConcurrentHashMap$Segment[] segments = this.segments;
        int[] mc = new int[segments.length];
        int mcsum = 0;
        for (int i = 0; i < segments.length; ++i) {
            if (segments[i].count != 0) return false; else mcsum += (mc[i] = segments[i].modCount);
        }
        if (mcsum != 0) {
            for (int i = 0; i < segments.length; ++i) {
                if (segments[i].count != 0 || mc[i] != segments[i].modCount) return false;
            }
        }
        return true;
    }
    
    public int size() {
        final ConcurrentHashMap$Segment[] segments = this.segments;
        long sum = 0;
        long check = 0;
        int[] mc = new int[segments.length];
        for (int k = 0; k < RETRIES_BEFORE_LOCK; ++k) {
            check = 0;
            sum = 0;
            int mcsum = 0;
            for (int i = 0; i < segments.length; ++i) {
                sum += segments[i].count;
                mcsum += (mc[i] = segments[i].modCount);
            }
            if (mcsum != 0) {
                for (int i = 0; i < segments.length; ++i) {
                    check += segments[i].count;
                    if (mc[i] != segments[i].modCount) {
                        check = -1;
                        break;
                    }
                }
            }
            if (check == sum) break;
        }
        if (check != sum) {
            sum = 0;
            for (int i = 0; i < segments.length; ++i) segments[i].lock();
            for (int i = 0; i < segments.length; ++i) sum += segments[i].count;
            for (int i = 0; i < segments.length; ++i) segments[i].unlock();
        }
        if (sum > Integer.MAX_VALUE) return Integer.MAX_VALUE; else return (int)sum;
    }
    
    public Object get(Object key) {
        int hash = hash(key);
        return segmentFor(hash).get(key, hash);
    }
    
    public boolean containsKey(Object key) {
        int hash = hash(key);
        return segmentFor(hash).containsKey(key, hash);
    }
    
    public boolean containsValue(Object value) {
        if (value == null) throw new NullPointerException();
        final ConcurrentHashMap$Segment[] segments = this.segments;
        int[] mc = new int[segments.length];
        for (int k = 0; k < RETRIES_BEFORE_LOCK; ++k) {
            int sum = 0;
            int mcsum = 0;
            for (int i = 0; i < segments.length; ++i) {
                int c = segments[i].count;
                mcsum += (mc[i] = segments[i].modCount);
                if (segments[i].containsValue(value)) return true;
            }
            boolean cleanSweep = true;
            if (mcsum != 0) {
                for (int i = 0; i < segments.length; ++i) {
                    int c = segments[i].count;
                    if (mc[i] != segments[i].modCount) {
                        cleanSweep = false;
                        break;
                    }
                }
            }
            if (cleanSweep) return false;
        }
        for (int i = 0; i < segments.length; ++i) segments[i].lock();
        boolean found = false;
        try {
            for (int i = 0; i < segments.length; ++i) {
                if (segments[i].containsValue(value)) {
                    found = true;
                    break;
                }
            }
        } finally {
            for (int i = 0; i < segments.length; ++i) segments[i].unlock();
        }
        return found;
    }
    
    public boolean contains(Object value) {
        return containsValue(value);
    }
    
    public Object put(Object key, Object value) {
        if (value == null) throw new NullPointerException();
        int hash = hash(key);
        return segmentFor(hash).put(key, hash, value, false);
    }
    
    public Object putIfAbsent(Object key, Object value) {
        if (value == null) throw new NullPointerException();
        int hash = hash(key);
        return segmentFor(hash).put(key, hash, value, true);
    }
    
    public void putAll(Map t) {
        for (Iterator it = (Iterator)t.entrySet().iterator(); it.hasNext(); ) {
            Map$Entry e = (Map$Entry)it.next();
            put(e.getKey(), e.getValue());
        }
    }
    
    public Object remove(Object key) {
        int hash = hash(key);
        return segmentFor(hash).remove(key, hash, null);
    }
    
    public boolean remove(Object key, Object value) {
        int hash = hash(key);
        return segmentFor(hash).remove(key, hash, value) != null;
    }
    
    public boolean replace(Object key, Object oldValue, Object newValue) {
        if (oldValue == null || newValue == null) throw new NullPointerException();
        int hash = hash(key);
        return segmentFor(hash).replace(key, hash, oldValue, newValue);
    }
    
    public Object replace(Object key, Object value) {
        if (value == null) throw new NullPointerException();
        int hash = hash(key);
        return segmentFor(hash).replace(key, hash, value);
    }
    
    public void clear() {
        for (int i = 0; i < segments.length; ++i) segments[i].clear();
    }
    
    public Set keySet() {
        Set ks = keySet;
        return (ks != null) ? ks : (keySet = new ConcurrentHashMap$KeySet(this));
    }
    
    public Collection values() {
        Collection vs = values;
        return (vs != null) ? vs : (values = new ConcurrentHashMap$Values(this));
    }
    
    public Set entrySet() {
        Set es = entrySet;
        return (es != null) ? es : (entrySet = (Set)(Set)new ConcurrentHashMap$EntrySet(this));
    }
    
    public Enumeration keys() {
        return new ConcurrentHashMap$KeyIterator(this);
    }
    
    public Enumeration elements() {
        return new ConcurrentHashMap$ValueIterator(this);
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
    {
    }
    {
    }
    {
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        for (int k = 0; k < segments.length; ++k) {
            ConcurrentHashMap$Segment seg = (ConcurrentHashMap$Segment)segments[k];
            seg.lock();
            try {
                ConcurrentHashMap$HashEntry[] tab = seg.table;
                for (int i = 0; i < tab.length; ++i) {
                    for (ConcurrentHashMap$HashEntry e = (ConcurrentHashMap$HashEntry)tab[i]; e != null; e = e.next) {
                        s.writeObject(e.key);
                        s.writeObject(e.value);
                    }
                }
            } finally {
                seg.unlock();
            }
        }
        s.writeObject(null);
        s.writeObject(null);
    }
    
    private void readObject(java.io.ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        for (int i = 0; i < segments.length; ++i) {
            segments[i].setTable(new ConcurrentHashMap$HashEntry[1]);
        }
        for (; ; ) {
            Object key = (Object)s.readObject();
            Object value = (Object)s.readObject();
            if (key == null) break;
            put(key, value);
        }
    }
}
