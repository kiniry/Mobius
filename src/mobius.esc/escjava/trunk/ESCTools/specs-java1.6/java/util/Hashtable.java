package java.util;

import java.io.*;

public class Hashtable extends Dictionary implements Map, Cloneable, java.io.Serializable {
    
    /*synthetic*/ static int access$508(Hashtable x0) {
        return x0.modCount++;
    }
    
    /*synthetic*/ static int access$500(Hashtable x0) {
        return x0.modCount;
    }
    
    /*synthetic*/ static Hashtable.Entry[] access$400(Hashtable x0) {
        return x0.table;
    }
    
    /*synthetic*/ static int access$210(Hashtable x0) {
        return x0.count--;
    }
    
    /*synthetic*/ static int access$200(Hashtable x0) {
        return x0.count;
    }
    
    /*synthetic*/ static Iterator access$100(Hashtable x0, int x1) {
        return x0.getIterator(x1);
    }
    {
    }
    private transient Hashtable$Entry[] table;
    private transient int count;
    private int threshold;
    private float loadFactor;
    private transient int modCount = 0;
    private static final long serialVersionUID = 1421746759512286392L;
    
    public Hashtable(int initialCapacity, float loadFactor) {
        
        if (initialCapacity < 0) throw new IllegalArgumentException("Illegal Capacity: " + initialCapacity);
        if (loadFactor <= 0 || Float.isNaN(loadFactor)) throw new IllegalArgumentException("Illegal Load: " + loadFactor);
        if (initialCapacity == 0) initialCapacity = 1;
        this.loadFactor = loadFactor;
        table = new Hashtable$Entry[initialCapacity];
        threshold = (int)(initialCapacity * loadFactor);
    }
    
    public Hashtable(int initialCapacity) {
        this(initialCapacity, 0.75F);
    }
    
    public Hashtable() {
        this(11, 0.75F);
    }
    
    public Hashtable(Map t) {
        this(Math.max(2 * t.size(), 11), 0.75F);
        putAll(t);
    }
    
    public synchronized int size() {
        return count;
    }
    
    public synchronized boolean isEmpty() {
        return count == 0;
    }
    
    public synchronized Enumeration keys() {
        return this.getEnumeration(KEYS);
    }
    
    public synchronized Enumeration elements() {
        return this.getEnumeration(VALUES);
    }
    
    public synchronized boolean contains(Object value) {
        if (value == null) {
            throw new NullPointerException();
        }
        Hashtable$Entry[] tab = table;
        for (int i = tab.length; i-- > 0; ) {
            for (Hashtable$Entry e = tab[i]; e != null; e = e.next) {
                if (e.value.equals(value)) {
                    return true;
                }
            }
        }
        return false;
    }
    
    public boolean containsValue(Object value) {
        return contains(value);
    }
    
    public synchronized boolean containsKey(Object key) {
        Hashtable$Entry[] tab = table;
        int hash = key.hashCode();
        int index = (hash & 2147483647) % tab.length;
        for (Hashtable$Entry e = tab[index]; e != null; e = e.next) {
            if ((e.hash == hash) && e.key.equals(key)) {
                return true;
            }
        }
        return false;
    }
    
    public synchronized Object get(Object key) {
        Hashtable$Entry[] tab = table;
        int hash = key.hashCode();
        int index = (hash & 2147483647) % tab.length;
        for (Hashtable$Entry e = tab[index]; e != null; e = e.next) {
            if ((e.hash == hash) && e.key.equals(key)) {
                return e.value;
            }
        }
        return null;
    }
    
    protected void rehash() {
        int oldCapacity = table.length;
        Hashtable$Entry[] oldMap = table;
        int newCapacity = oldCapacity * 2 + 1;
        Hashtable$Entry[] newMap = new Hashtable$Entry[newCapacity];
        modCount++;
        threshold = (int)(newCapacity * loadFactor);
        table = newMap;
        for (int i = oldCapacity; i-- > 0; ) {
            for (Hashtable$Entry old = oldMap[i]; old != null; ) {
                Hashtable$Entry e = old;
                old = old.next;
                int index = (e.hash & 2147483647) % newCapacity;
                e.next = newMap[index];
                newMap[index] = e;
            }
        }
    }
    
    public synchronized Object put(Object key, Object value) {
        if (value == null) {
            throw new NullPointerException();
        }
        Hashtable$Entry[] tab = table;
        int hash = key.hashCode();
        int index = (hash & 2147483647) % tab.length;
        for (Hashtable$Entry e = tab[index]; e != null; e = e.next) {
            if ((e.hash == hash) && e.key.equals(key)) {
                Object old = e.value;
                e.value = value;
                return old;
            }
        }
        modCount++;
        if (count >= threshold) {
            rehash();
            tab = table;
            index = (hash & 2147483647) % tab.length;
        }
        Hashtable$Entry e = tab[index];
        tab[index] = new Hashtable$Entry(hash, key, value, e);
        count++;
        return null;
    }
    
    public synchronized Object remove(Object key) {
        Hashtable$Entry[] tab = table;
        int hash = key.hashCode();
        int index = (hash & 2147483647) % tab.length;
        for (Hashtable$Entry e = tab[index], prev = null; e != null; prev = e, e = e.next) {
            if ((e.hash == hash) && e.key.equals(key)) {
                modCount++;
                if (prev != null) {
                    prev.next = e.next;
                } else {
                    tab[index] = e.next;
                }
                count--;
                Object oldValue = e.value;
                e.value = null;
                return oldValue;
            }
        }
        return null;
    }
    
    public synchronized void putAll(Map t) {
        Iterator i = t.entrySet().iterator();
        while (i.hasNext()) {
            Map$Entry e = (Map$Entry)i.next();
            put(e.getKey(), e.getValue());
        }
    }
    
    public synchronized void clear() {
        Hashtable$Entry[] tab = table;
        modCount++;
        for (int index = tab.length; --index >= 0; ) tab[index] = null;
        count = 0;
    }
    
    public synchronized Object clone() {
        try {
            Hashtable t = (Hashtable)(Hashtable)super.clone();
            t.table = new Hashtable$Entry[table.length];
            for (int i = table.length; i-- > 0; ) {
                t.table[i] = (table[i] != null) ? (Hashtable$Entry)(Hashtable$Entry)table[i].clone() : null;
            }
            t.keySet = null;
            t.entrySet = null;
            t.values = null;
            t.modCount = 0;
            return t;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    public synchronized String toString() {
        int max = size() - 1;
        StringBuffer buf = new StringBuffer();
        Iterator it = entrySet().iterator();
        buf.append("{");
        for (int i = 0; i <= max; i++) {
            Map$Entry e = (Map$Entry)it.next();
            Object key = e.getKey();
            Object value = e.getValue();
            buf.append((key == this ? "(this Map)" : ("" + key)) + "=" + (value == this ? "(this Map)" : ("" + value)));
            if (i < max) buf.append(", ");
        }
        buf.append("}");
        return buf.toString();
    }
    
    private Enumeration getEnumeration(int type) {
        if (count == 0) {
            return (Enumeration)emptyEnumerator;
        } else {
            return new Hashtable$Enumerator(this, type, false);
        }
    }
    
    private Iterator getIterator(int type) {
        if (count == 0) {
            return (Iterator)emptyIterator;
        } else {
            return new Hashtable$Enumerator(this, type, true);
        }
    }
    private volatile transient Set keySet = null;
    private volatile transient Set entrySet = null;
    private volatile transient Collection values = null;
    
    public Set keySet() {
        if (keySet == null) keySet = Collections.synchronizedSet(new Hashtable$KeySet(this, null), this);
        return keySet;
    }
    {
    }
    
    public Set entrySet() {
        if (entrySet == null) entrySet = Collections.synchronizedSet(new Hashtable$EntrySet(this, null), this);
        return entrySet;
    }
    {
    }
    
    public Collection values() {
        if (values == null) values = Collections.synchronizedCollection(new Hashtable$ValueCollection(this, null), this);
        return values;
    }
    {
    }
    
    public synchronized boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof Map)) return false;
        Map t = (Map)(Map)o;
        if (t.size() != size()) return false;
        try {
            Iterator i = entrySet().iterator();
            while (i.hasNext()) {
                Map$Entry e = (Map$Entry)i.next();
                Object key = e.getKey();
                Object value = e.getValue();
                if (value == null) {
                    if (!(t.get(key) == null && t.containsKey(key))) return false;
                } else {
                    if (!value.equals(t.get(key))) return false;
                }
            }
        } catch (ClassCastException unused) {
            return false;
        } catch (NullPointerException unused) {
            return false;
        }
        return true;
    }
    
    public synchronized int hashCode() {
        int h = 0;
        if (count == 0 || loadFactor < 0) return h;
        loadFactor = -loadFactor;
        Hashtable$Entry[] tab = table;
        for (int i = 0; i < tab.length; i++) for (Hashtable$Entry e = tab[i]; e != null; e = e.next) h += e.key.hashCode() ^ e.value.hashCode();
        loadFactor = -loadFactor;
        return h;
    }
    
    private synchronized void writeObject(java.io.ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        s.writeInt(table.length);
        s.writeInt(count);
        for (int index = table.length - 1; index >= 0; index--) {
            Hashtable$Entry entry = table[index];
            while (entry != null) {
                s.writeObject(entry.key);
                s.writeObject(entry.value);
                entry = entry.next;
            }
        }
    }
    
    private void readObject(java.io.ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        int origlength = s.readInt();
        int elements = s.readInt();
        int length = (int)(elements * loadFactor) + (elements / 20) + 3;
        if (length > elements && (length & 1) == 0) length--;
        if (origlength > 0 && length > origlength) length = origlength;
        table = new Hashtable$Entry[length];
        count = 0;
        for (; elements > 0; elements--) {
            Object key = (Object)s.readObject();
            Object value = (Object)s.readObject();
            reconstitutionPut(key, value);
        }
    }
    
    private void reconstitutionPut(Object key, Object value) throws StreamCorruptedException {
        if (value == null) {
            throw new java.io.StreamCorruptedException();
        }
        Hashtable$Entry[] tab = table;
        int hash = key.hashCode();
        int index = (hash & 2147483647) % tab.length;
        for (Hashtable$Entry e = tab[index]; e != null; e = e.next) {
            if ((e.hash == hash) && e.key.equals(key)) {
                throw new java.io.StreamCorruptedException();
            }
        }
        Hashtable$Entry e = tab[index];
        tab[index] = new Hashtable$Entry(hash, key, value, e);
        count++;
    }
    {
    }
    private static final int KEYS = 0;
    private static final int VALUES = 1;
    private static final int ENTRIES = 2;
    {
    }
    private static Enumeration emptyEnumerator = new Hashtable$EmptyEnumerator();
    private static Iterator emptyIterator = new Hashtable$EmptyIterator();
    {
    }
    {
    }
}
