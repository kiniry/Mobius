package java.io;

import java.util.Arrays;

class ObjectOutputStream$HandleTable {
    private int size;
    private int threshold;
    private final float loadFactor;
    private int[] spine;
    private int[] next;
    private Object[] objs;
    
    ObjectOutputStream$HandleTable(int initialCapacity, float loadFactor) {
        
        this.loadFactor = loadFactor;
        spine = new int[initialCapacity];
        next = new int[initialCapacity];
        objs = new Object[initialCapacity];
        threshold = (int)(initialCapacity * loadFactor);
        clear();
    }
    
    int assign(Object obj) {
        if (size >= next.length) {
            growEntries();
        }
        if (size >= threshold) {
            growSpine();
        }
        insert(obj, size);
        return size++;
    }
    
    int lookup(Object obj) {
        if (size == 0) {
            return -1;
        }
        int index = hash(obj) % spine.length;
        for (int i = spine[index]; i >= 0; i = next[i]) {
            if (objs[i] == obj) {
                return i;
            }
        }
        return -1;
    }
    
    void clear() {
        Arrays.fill(spine, -1);
        Arrays.fill(objs, 0, size, null);
        size = 0;
    }
    
    int size() {
        return size;
    }
    
    private void insert(Object obj, int handle) {
        int index = hash(obj) % spine.length;
        objs[handle] = obj;
        next[handle] = spine[index];
        spine[index] = handle;
    }
    
    private void growSpine() {
        spine = new int[(spine.length << 1) + 1];
        threshold = (int)(spine.length * loadFactor);
        Arrays.fill(spine, -1);
        for (int i = 0; i < size; i++) {
            insert(objs[i], i);
        }
    }
    
    private void growEntries() {
        int newLength = (next.length << 1) + 1;
        int[] newNext = new int[newLength];
        System.arraycopy(next, 0, newNext, 0, size);
        next = newNext;
        Object[] newObjs = new Object[newLength];
        System.arraycopy(objs, 0, newObjs, 0, size);
        objs = newObjs;
    }
    
    private int hash(Object obj) {
        return System.identityHashCode(obj) & 2147483647;
    }
}
