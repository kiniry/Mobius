package java.io;

import java.util.Arrays;

class ObjectOutputStream$ReplaceTable {
    private final ObjectOutputStream$HandleTable htab;
    private Object[] reps;
    
    ObjectOutputStream$ReplaceTable(int initialCapacity, float loadFactor) {
        
        htab = new ObjectOutputStream$HandleTable(initialCapacity, loadFactor);
        reps = new Object[initialCapacity];
    }
    
    void assign(Object obj, Object repo) {
        int index = htab.assign(obj);
        while (index >= reps.length) {
            grow();
        }
        reps[index] = repo;
    }
    
    Object lookup(Object obj) {
        int index = htab.lookup(obj);
        return (index >= 0) ? reps[index] : obj;
    }
    
    void clear() {
        Arrays.fill(reps, 0, htab.size(), null);
        htab.clear();
    }
    
    int size() {
        return htab.size();
    }
    
    private void grow() {
        Object[] newReps = new Object[(reps.length << 1) + 1];
        System.arraycopy(reps, 0, newReps, 0, reps.length);
        reps = newReps;
    }
}
