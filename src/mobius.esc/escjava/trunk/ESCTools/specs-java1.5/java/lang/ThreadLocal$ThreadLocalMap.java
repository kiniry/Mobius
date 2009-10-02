package java.lang;

import java.lang.ref.*;

class ThreadLocal$ThreadLocalMap {
    
    /*synthetic*/ ThreadLocal$ThreadLocalMap(ThreadLocal.ThreadLocalMap x0, java.lang.ThreadLocal$1 x1) {
        this(x0);
    }
    
    /*synthetic*/ static void access$200(ThreadLocal$ThreadLocalMap x0, ThreadLocal x1) {
        x0.remove(x1);
    }
    
    /*synthetic*/ static void access$100(ThreadLocal$ThreadLocalMap x0, ThreadLocal x1, Object x2) {
        x0.set(x1, x2);
    }
    
    /*synthetic*/ static Object access$000(ThreadLocal$ThreadLocalMap x0, ThreadLocal x1) {
        return x0.get(x1);
    }
    {
    }
    private static final int INITIAL_CAPACITY = 16;
    private ThreadLocal$ThreadLocalMap$Entry[] table;
    private int size = 0;
    private int threshold;
    
    private void setThreshold(int len) {
        threshold = len * 2 / 3;
    }
    
    private static int nextIndex(int i, int len) {
        return ((i + 1 < len) ? i + 1 : 0);
    }
    
    private static int prevIndex(int i, int len) {
        return ((i - 1 >= 0) ? i - 1 : len - 1);
    }
    
    ThreadLocal$ThreadLocalMap(ThreadLocal firstKey, Object firstValue) {
        
        table = new ThreadLocal$ThreadLocalMap$Entry[INITIAL_CAPACITY];
        int i = ThreadLocal.access$400(firstKey) & (INITIAL_CAPACITY - 1);
        table[i] = new ThreadLocal$ThreadLocalMap$Entry(firstKey, firstValue, null);
        size = 1;
        setThreshold(INITIAL_CAPACITY);
    }
    
    private ThreadLocal$ThreadLocalMap(ThreadLocal$ThreadLocalMap parentMap) {
        
        ThreadLocal$ThreadLocalMap$Entry[] parentTable = parentMap.table;
        int len = parentTable.length;
        setThreshold(len);
        table = new ThreadLocal$ThreadLocalMap$Entry[len];
        for (int j = 0; j < len; j++) {
            ThreadLocal$ThreadLocalMap$Entry e = parentTable[j];
            if (e != null) {
                ThreadLocal k = (ThreadLocal)e.get();
                if (k != null) {
                    ThreadLocal key = k;
                    Object value = key.childValue(ThreadLocal.ThreadLocalMap.Entry.access$600(e));
                    ThreadLocal$ThreadLocalMap$Entry c = new ThreadLocal$ThreadLocalMap$Entry(key, value, null);
                    int h = ThreadLocal.access$400(key) & (len - 1);
                    while (table[h] != null) h = nextIndex(h, len);
                    table[h] = c;
                    size++;
                }
            }
        }
    }
    
    private Object get(ThreadLocal key) {
        int i = ThreadLocal.access$400(key) & (table.length - 1);
        ThreadLocal$ThreadLocalMap$Entry e = table[i];
        if (e != null && e.get() == key) return ThreadLocal.ThreadLocalMap.Entry.access$600(e);
        return getAfterMiss(key, i, e);
    }
    
    private Object getAfterMiss(ThreadLocal key, int i, ThreadLocal$ThreadLocalMap$Entry e) {
        ThreadLocal$ThreadLocalMap$Entry[] tab = table;
        int len = tab.length;
        while (e != null) {
            ThreadLocal k = (ThreadLocal)e.get();
            if (k == key) return ThreadLocal.ThreadLocalMap.Entry.access$600(e);
            if (k == null) return replaceStaleEntry(key, null, i, true);
            i = nextIndex(i, len);
            e = tab[i];
        }
        Object value = key.initialValue();
        tab[i] = new ThreadLocal$ThreadLocalMap$Entry(key, value, null);
        int sz = ++size;
        if (!cleanSomeSlots(i, sz) && sz >= threshold) rehash();
        return value;
    }
    
    private void set(ThreadLocal key, Object value) {
        ThreadLocal$ThreadLocalMap$Entry[] tab = table;
        int len = tab.length;
        int i = ThreadLocal.access$400(key) & (len - 1);
        for (ThreadLocal$ThreadLocalMap$Entry e = tab[i]; e != null; e = tab[i = nextIndex(i, len)]) {
            ThreadLocal k = (ThreadLocal)e.get();
            if (k == key) {
                ThreadLocal.ThreadLocalMap.Entry.access$602(e, value);
                return;
            }
            if (k == null) {
                replaceStaleEntry(key, value, i, false);
                return;
            }
        }
        tab[i] = new ThreadLocal$ThreadLocalMap$Entry(key, value, null);
        int sz = ++size;
        if (!cleanSomeSlots(i, sz) && sz >= threshold) rehash();
    }
    
    private void remove(ThreadLocal key) {
        ThreadLocal$ThreadLocalMap$Entry[] tab = table;
        int len = tab.length;
        int i = ThreadLocal.access$400(key) & (len - 1);
        for (ThreadLocal$ThreadLocalMap$Entry e = tab[i]; e != null; e = tab[i = nextIndex(i, len)]) {
            if (e.get() == key) {
                e.clear();
                expungeStaleEntry(i);
                return;
            }
        }
    }
    
    private Object replaceStaleEntry(ThreadLocal key, Object value, int staleSlot, boolean actAsGet) {
        ThreadLocal$ThreadLocalMap$Entry[] tab = table;
        int len = tab.length;
        ThreadLocal$ThreadLocalMap$Entry e;
        int slotToExpunge = staleSlot;
        for (int i = prevIndex(staleSlot, len); (e = tab[i]) != null; i = prevIndex(i, len)) if (e.get() == null) slotToExpunge = i;
        for (int i = nextIndex(staleSlot, len); (e = tab[i]) != null; i = nextIndex(i, len)) {
            ThreadLocal k = (ThreadLocal)e.get();
            if (k == key) {
                if (actAsGet) value = ThreadLocal.ThreadLocalMap.Entry.access$600(e); else ThreadLocal.ThreadLocalMap.Entry.access$602(e, value);
                tab[i] = tab[staleSlot];
                tab[staleSlot] = e;
                if (slotToExpunge == staleSlot) slotToExpunge = i;
                cleanSomeSlots(expungeStaleEntry(slotToExpunge), len);
                return value;
            }
            if (k == null && slotToExpunge == staleSlot) slotToExpunge = i;
        }
        if (actAsGet) value = key.initialValue();
        ThreadLocal.ThreadLocalMap.Entry.access$602(tab[staleSlot], null);
        tab[staleSlot] = new ThreadLocal$ThreadLocalMap$Entry(key, value, null);
        if (slotToExpunge != staleSlot) cleanSomeSlots(expungeStaleEntry(slotToExpunge), len);
        return value;
    }
    
    private int expungeStaleEntry(int staleSlot) {
        ThreadLocal$ThreadLocalMap$Entry[] tab = table;
        int len = tab.length;
        ThreadLocal.ThreadLocalMap.Entry.access$602(tab[staleSlot], null);
        tab[staleSlot] = null;
        size--;
        ThreadLocal$ThreadLocalMap$Entry e;
        int i;
        for (i = nextIndex(staleSlot, len); (e = tab[i]) != null; i = nextIndex(i, len)) {
            ThreadLocal k = (ThreadLocal)e.get();
            if (k == null) {
                ThreadLocal.ThreadLocalMap.Entry.access$602(e, null);
                tab[i] = null;
                size--;
            } else {
                ThreadLocal key = k;
                int h = ThreadLocal.access$400(key) & (len - 1);
                if (h != i) {
                    tab[i] = null;
                    while (tab[h] != null) h = nextIndex(h, len);
                    tab[h] = e;
                }
            }
        }
        return i;
    }
    
    private boolean cleanSomeSlots(int i, int n) {
        boolean removed = false;
        ThreadLocal$ThreadLocalMap$Entry[] tab = table;
        int len = tab.length;
        do {
            i = nextIndex(i, len);
            ThreadLocal$ThreadLocalMap$Entry e = tab[i];
            if (e != null && e.get() == null) {
                n = len;
                removed = true;
                i = expungeStaleEntry(i);
            }
        }         while ((n >>>= 1) != 0);
        return removed;
    }
    
    private void rehash() {
        expungeStaleEntries();
        if (size >= threshold - threshold / 4) resize();
    }
    
    private void resize() {
        ThreadLocal$ThreadLocalMap$Entry[] oldTab = table;
        int oldLen = oldTab.length;
        int newLen = oldLen * 2;
        ThreadLocal$ThreadLocalMap$Entry[] newTab = new ThreadLocal$ThreadLocalMap$Entry[newLen];
        int count = 0;
        for (int j = 0; j < oldLen; ++j) {
            ThreadLocal$ThreadLocalMap$Entry e = oldTab[j];
            oldTab[j] = null;
            if (e != null) {
                ThreadLocal k = (ThreadLocal)e.get();
                if (k == null) {
                    ThreadLocal.ThreadLocalMap.Entry.access$602(e, null);
                } else {
                    ThreadLocal key = k;
                    int h = ThreadLocal.access$400(key) & (newLen - 1);
                    while (newTab[h] != null) h = nextIndex(h, newLen);
                    newTab[h] = e;
                    count++;
                }
            }
        }
        setThreshold(newLen);
        size = count;
        table = newTab;
    }
    
    private void expungeStaleEntries() {
        ThreadLocal$ThreadLocalMap$Entry[] tab = table;
        int len = tab.length;
        for (int j = 0; j < len; j++) {
            ThreadLocal$ThreadLocalMap$Entry e = tab[j];
            if (e != null && e.get() == null) expungeStaleEntry(j);
        }
    }
}
