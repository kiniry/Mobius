package java.util;

import java.io.*;

public class IdentityHashMap extends AbstractMap implements Map, java.io.Serializable, Cloneable {
    
    /*synthetic*/ static boolean access$1400(IdentityHashMap x0, Object x1, Object x2) {
        return x0.removeMapping(x1, x2);
    }
    
    /*synthetic*/ static boolean access$1300(IdentityHashMap x0, Object x1, Object x2) {
        return x0.containsMapping(x1, x2);
    }
    
    /*synthetic*/ static Object access$600(Object x0) {
        return unmaskNull(x0);
    }
    
    /*synthetic*/ static int access$400(Object x0, int x1) {
        return hash(x0, x1);
    }
    
    /*synthetic*/ static int access$300(int x0, int x1) {
        return nextKeyIndex(x0, x1);
    }
    
    /*synthetic*/ static int access$204(IdentityHashMap x0) {
        return ++x0.modCount;
    }
    
    /*synthetic*/ static int access$200(IdentityHashMap x0) {
        return x0.modCount;
    }
    
    /*synthetic*/ static Object[] access$100(IdentityHashMap x0) {
        return x0.table;
    }
    
    /*synthetic*/ static int access$010(IdentityHashMap x0) {
        return x0.size--;
    }
    
    /*synthetic*/ static int access$000(IdentityHashMap x0) {
        return x0.size;
    }
    {
    }
    private static final int DEFAULT_CAPACITY = 32;
    private static final int MINIMUM_CAPACITY = 4;
    private static final int MAXIMUM_CAPACITY = 1 << 29;
    private transient Object[] table;
    private int size;
    private volatile transient int modCount;
    private transient int threshold;
    private static final Object NULL_KEY = new Object();
    
    private static Object maskNull(Object key) {
        return (key == null ? NULL_KEY : key);
    }
    
    private static Object unmaskNull(Object key) {
        return (key == NULL_KEY ? null : key);
    }
    
    public IdentityHashMap() {
        
        init(DEFAULT_CAPACITY);
    }
    
    public IdentityHashMap(int expectedMaxSize) {
        
        if (expectedMaxSize < 0) throw new IllegalArgumentException("expectedMaxSize is negative: " + expectedMaxSize);
        init(capacity(expectedMaxSize));
    }
    
    private int capacity(int expectedMaxSize) {
        int minCapacity = (3 * expectedMaxSize) / 2;
        int result;
        if (minCapacity > MAXIMUM_CAPACITY || minCapacity < 0) {
            result = MAXIMUM_CAPACITY;
        } else {
            result = MINIMUM_CAPACITY;
            while (result < minCapacity) result <<= 1;
        }
        return result;
    }
    
    private void init(int initCapacity) {
        threshold = (initCapacity * 2) / 3;
        table = new Object[2 * initCapacity];
    }
    
    public IdentityHashMap(Map m) {
        this((int)((1 + m.size()) * 1.1));
        putAll(m);
    }
    
    public int size() {
        return size;
    }
    
    public boolean isEmpty() {
        return size == 0;
    }
    
    private static int hash(Object x, int length) {
        int h = System.identityHashCode(x);
        return ((h << 1) - (h << 8)) & (length - 1);
    }
    
    private static int nextKeyIndex(int i, int len) {
        return (i + 2 < len ? i + 2 : 0);
    }
    
    public Object get(Object key) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);
        while (true) {
            Object item = tab[i];
            if (item == k) return (Object)tab[i + 1];
            if (item == null) return null;
            i = nextKeyIndex(i, len);
        }
    }
    
    public boolean containsKey(Object key) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);
        while (true) {
            Object item = tab[i];
            if (item == k) return true;
            if (item == null) return false;
            i = nextKeyIndex(i, len);
        }
    }
    
    public boolean containsValue(Object value) {
        Object[] tab = table;
        for (int i = 1; i < tab.length; i += 2) if (tab[i] == value) return true;
        return false;
    }
    
    private boolean containsMapping(Object key, Object value) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);
        while (true) {
            Object item = tab[i];
            if (item == k) return tab[i + 1] == value;
            if (item == null) return false;
            i = nextKeyIndex(i, len);
        }
    }
    
    public Object put(Object key, Object value) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);
        Object item;
        while ((item = tab[i]) != null) {
            if (item == k) {
                Object oldValue = (Object)tab[i + 1];
                tab[i + 1] = value;
                return oldValue;
            }
            i = nextKeyIndex(i, len);
        }
        modCount++;
        tab[i] = k;
        tab[i + 1] = value;
        if (++size >= threshold) resize(len);
        return null;
    }
    
    private void resize(int newCapacity) {
        int newLength = newCapacity * 2;
        Object[] oldTable = table;
        int oldLength = oldTable.length;
        if (oldLength == 2 * MAXIMUM_CAPACITY) {
            if (threshold == MAXIMUM_CAPACITY - 1) throw new IllegalStateException("Capacity exhausted.");
            threshold = MAXIMUM_CAPACITY - 1;
            return;
        }
        if (oldLength >= newLength) return;
        Object[] newTable = new Object[newLength];
        threshold = newLength / 3;
        for (int j = 0; j < oldLength; j += 2) {
            Object key = oldTable[j];
            if (key != null) {
                Object value = oldTable[j + 1];
                oldTable[j] = null;
                oldTable[j + 1] = null;
                int i = hash(key, newLength);
                while (newTable[i] != null) i = nextKeyIndex(i, newLength);
                newTable[i] = key;
                newTable[i + 1] = value;
            }
        }
        table = newTable;
    }
    
    public void putAll(Map t) {
        int n = t.size();
        if (n == 0) return;
        if (n > threshold) resize(capacity(n));
        for (Iterator i$ = t.entrySet().iterator(); i$.hasNext(); ) {
            Map$Entry e = (Map$Entry)i$.next();
            put(e.getKey(), e.getValue());
        }
    }
    
    public Object remove(Object key) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);
        while (true) {
            Object item = tab[i];
            if (item == k) {
                modCount++;
                size--;
                Object oldValue = (Object)tab[i + 1];
                tab[i + 1] = null;
                tab[i] = null;
                closeDeletion(i);
                return oldValue;
            }
            if (item == null) return null;
            i = nextKeyIndex(i, len);
        }
    }
    
    private boolean removeMapping(Object key, Object value) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);
        while (true) {
            Object item = tab[i];
            if (item == k) {
                if (tab[i + 1] != value) return false;
                modCount++;
                size--;
                tab[i] = null;
                tab[i + 1] = null;
                closeDeletion(i);
                return true;
            }
            if (item == null) return false;
            i = nextKeyIndex(i, len);
        }
    }
    
    private void closeDeletion(int d) {
        Object[] tab = table;
        int len = tab.length;
        Object item;
        for (int i = nextKeyIndex(d, len); (item = tab[i]) != null; i = nextKeyIndex(i, len)) {
            int r = hash(item, len);
            if ((i < r && (r <= d || d <= i)) || (r <= d && d <= i)) {
                tab[d] = item;
                tab[d + 1] = tab[i + 1];
                tab[i] = null;
                tab[i + 1] = null;
                d = i;
            }
        }
    }
    
    public void clear() {
        modCount++;
        Object[] tab = table;
        for (int i = 0; i < tab.length; i++) tab[i] = null;
        size = 0;
    }
    
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        } else if (o instanceof IdentityHashMap) {
            IdentityHashMap m = (IdentityHashMap)(IdentityHashMap)o;
            if (m.size() != size) return false;
            Object[] tab = m.table;
            for (int i = 0; i < tab.length; i += 2) {
                Object k = tab[i];
                if (k != null && !containsMapping(k, tab[i + 1])) return false;
            }
            return true;
        } else if (o instanceof Map) {
            Map m = (Map)(Map)o;
            return entrySet().equals(m.entrySet());
        } else {
            return false;
        }
    }
    
    public int hashCode() {
        int result = 0;
        Object[] tab = table;
        for (int i = 0; i < tab.length; i += 2) {
            Object key = tab[i];
            if (key != null) {
                Object k = unmaskNull(key);
                result += System.identityHashCode(k) ^ System.identityHashCode(tab[i + 1]);
            }
        }
        return result;
    }
    
    public Object clone() {
        try {
            IdentityHashMap t = (IdentityHashMap)(IdentityHashMap)super.clone();
            t.entrySet = null;
            t.table = (Object[])(Object[])table.clone();
            return t;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
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
        if (ks != null) return ks; else return keySet = new IdentityHashMap$KeySet(this, null);
    }
    {
    }
    
    public Collection values() {
        Collection vs = values;
        if (vs != null) return vs; else return values = new IdentityHashMap$Values(this, null);
    }
    {
    }
    
    public Set entrySet() {
        Set es = entrySet;
        if (es != null) return es; else return entrySet = new IdentityHashMap$EntrySet(this, null);
    }
    {
    }
    private static final long serialVersionUID = 8188218128353913216L;
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        s.defaultWriteObject();
        s.writeInt(size);
        Object[] tab = table;
        for (int i = 0; i < tab.length; i += 2) {
            Object key = tab[i];
            if (key != null) {
                s.writeObject(unmaskNull(key));
                s.writeObject(tab[i + 1]);
            }
        }
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        int size = s.readInt();
        init(capacity((size * 4) / 3));
        for (int i = 0; i < size; i++) {
            Object key = (Object)s.readObject();
            Object value = (Object)s.readObject();
            putForCreate(key, value);
        }
    }
    
    private void putForCreate(Object key, Object value) throws IOException {
        Object k = (Object)maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);
        Object item;
        while ((item = tab[i]) != null) {
            if (item == k) throw new java.io.StreamCorruptedException();
            i = nextKeyIndex(i, len);
        }
        tab[i] = k;
        tab[i + 1] = value;
    }
}
