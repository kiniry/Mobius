package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;
import java.io.Serializable;

final class ConcurrentHashMap$Segment extends ReentrantLock implements Serializable {
    private static final long serialVersionUID = 2249069246763182397L;
    volatile transient int count;
    transient int modCount;
    transient int threshold;
    volatile transient ConcurrentHashMap$HashEntry[] table;
    final float loadFactor;
    
    ConcurrentHashMap$Segment(int initialCapacity, float lf) {
        
        loadFactor = lf;
        setTable(new ConcurrentHashMap$HashEntry[initialCapacity]);
    }
    
    void setTable(ConcurrentHashMap$HashEntry[] newTable) {
        threshold = (int)(newTable.length * loadFactor);
        table = newTable;
    }
    
    ConcurrentHashMap$HashEntry getFirst(int hash) {
        ConcurrentHashMap$HashEntry[] tab = table;
        return (ConcurrentHashMap$HashEntry)tab[hash & (tab.length - 1)];
    }
    
    Object readValueUnderLock(ConcurrentHashMap$HashEntry e) {
        lock();
        try {
            return e.value;
        } finally {
            unlock();
        }
    }
    
    Object get(Object key, int hash) {
        if (count != 0) {
            ConcurrentHashMap$HashEntry e = getFirst(hash);
            while (e != null) {
                if (e.hash == hash && key.equals(e.key)) {
                    Object v = e.value;
                    if (v != null) return v;
                    return readValueUnderLock(e);
                }
                e = e.next;
            }
        }
        return null;
    }
    
    boolean containsKey(Object key, int hash) {
        if (count != 0) {
            ConcurrentHashMap$HashEntry e = getFirst(hash);
            while (e != null) {
                if (e.hash == hash && key.equals(e.key)) return true;
                e = e.next;
            }
        }
        return false;
    }
    
    boolean containsValue(Object value) {
        if (count != 0) {
            ConcurrentHashMap$HashEntry[] tab = table;
            int len = tab.length;
            for (int i = 0; i < len; i++) {
                for (ConcurrentHashMap$HashEntry e = (ConcurrentHashMap$HashEntry)tab[i]; e != null; e = e.next) {
                    Object v = e.value;
                    if (v == null) v = readValueUnderLock(e);
                    if (value.equals(v)) return true;
                }
            }
        }
        return false;
    }
    
    boolean replace(Object key, int hash, Object oldValue, Object newValue) {
        lock();
        try {
            ConcurrentHashMap$HashEntry e = getFirst(hash);
            while (e != null && (e.hash != hash || !key.equals(e.key))) e = e.next;
            boolean replaced = false;
            if (e != null && oldValue.equals(e.value)) {
                replaced = true;
                e.value = newValue;
            }
            return replaced;
        } finally {
            unlock();
        }
    }
    
    Object replace(Object key, int hash, Object newValue) {
        lock();
        try {
            ConcurrentHashMap$HashEntry e = getFirst(hash);
            while (e != null && (e.hash != hash || !key.equals(e.key))) e = e.next;
            Object oldValue = null;
            if (e != null) {
                oldValue = e.value;
                e.value = newValue;
            }
            return oldValue;
        } finally {
            unlock();
        }
    }
    
    Object put(Object key, int hash, Object value, boolean onlyIfAbsent) {
        lock();
        try {
            int c = count;
            if (c++ > threshold) rehash();
            ConcurrentHashMap$HashEntry[] tab = table;
            int index = hash & (tab.length - 1);
            ConcurrentHashMap$HashEntry first = (ConcurrentHashMap$HashEntry)tab[index];
            ConcurrentHashMap$HashEntry e = first;
            while (e != null && (e.hash != hash || !key.equals(e.key))) e = e.next;
            Object oldValue;
            if (e != null) {
                oldValue = e.value;
                if (!onlyIfAbsent) e.value = value;
            } else {
                oldValue = null;
                ++modCount;
                tab[index] = new ConcurrentHashMap$HashEntry(key, hash, first, value);
                count = c;
            }
            return oldValue;
        } finally {
            unlock();
        }
    }
    
    void rehash() {
        ConcurrentHashMap$HashEntry[] oldTable = table;
        int oldCapacity = oldTable.length;
        if (oldCapacity >= 1073741824) return;
        ConcurrentHashMap$HashEntry[] newTable = new ConcurrentHashMap$HashEntry[oldCapacity << 1];
        threshold = (int)(newTable.length * loadFactor);
        int sizeMask = newTable.length - 1;
        for (int i = 0; i < oldCapacity; i++) {
            ConcurrentHashMap$HashEntry e = (ConcurrentHashMap$HashEntry)oldTable[i];
            if (e != null) {
                ConcurrentHashMap$HashEntry next = e.next;
                int idx = e.hash & sizeMask;
                if (next == null) newTable[idx] = e; else {
                    ConcurrentHashMap$HashEntry lastRun = e;
                    int lastIdx = idx;
                    for (ConcurrentHashMap$HashEntry last = next; last != null; last = last.next) {
                        int k = last.hash & sizeMask;
                        if (k != lastIdx) {
                            lastIdx = k;
                            lastRun = last;
                        }
                    }
                    newTable[lastIdx] = lastRun;
                    for (ConcurrentHashMap$HashEntry p = e; p != lastRun; p = p.next) {
                        int k = p.hash & sizeMask;
                        ConcurrentHashMap$HashEntry n = (ConcurrentHashMap$HashEntry)newTable[k];
                        newTable[k] = new ConcurrentHashMap$HashEntry(p.key, p.hash, n, p.value);
                    }
                }
            }
        }
        table = newTable;
    }
    
    Object remove(Object key, int hash, Object value) {
        lock();
        try {
            int c = count - 1;
            ConcurrentHashMap$HashEntry[] tab = table;
            int index = hash & (tab.length - 1);
            ConcurrentHashMap$HashEntry first = (ConcurrentHashMap$HashEntry)tab[index];
            ConcurrentHashMap$HashEntry e = first;
            while (e != null && (e.hash != hash || !key.equals(e.key))) e = e.next;
            Object oldValue = null;
            if (e != null) {
                Object v = e.value;
                if (value == null || value.equals(v)) {
                    oldValue = v;
                    ++modCount;
                    ConcurrentHashMap$HashEntry newFirst = e.next;
                    for (ConcurrentHashMap$HashEntry p = first; p != e; p = p.next) newFirst = new ConcurrentHashMap$HashEntry(p.key, p.hash, newFirst, p.value);
                    tab[index] = newFirst;
                    count = c;
                }
            }
            return oldValue;
        } finally {
            unlock();
        }
    }
    
    void clear() {
        if (count != 0) {
            lock();
            try {
                ConcurrentHashMap$HashEntry[] tab = table;
                for (int i = 0; i < tab.length; i++) tab[i] = null;
                ++modCount;
                count = 0;
            } finally {
                unlock();
            }
        }
    }
}
