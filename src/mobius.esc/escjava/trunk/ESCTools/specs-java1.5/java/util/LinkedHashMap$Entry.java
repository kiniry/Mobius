package java.util;

import java.io.*;

class LinkedHashMap$Entry extends HashMap$Entry {
    
    /*synthetic*/ static void access$600(LinkedHashMap$Entry x0, LinkedHashMap$Entry x1) {
        x0.addBefore(x1);
    }
    LinkedHashMap$Entry before;
    LinkedHashMap$Entry after;
    
    LinkedHashMap$Entry(int hash, Object key, Object value, HashMap$Entry next) {
        super(hash, key, value, next);
    }
    
    private void remove() {
        before.after = after;
        after.before = before;
    }
    
    private void addBefore(LinkedHashMap$Entry existingEntry) {
        after = existingEntry;
        before = existingEntry.before;
        before.after = this;
        after.before = this;
    }
    
    void recordAccess(HashMap m) {
        LinkedHashMap lm = (LinkedHashMap)(LinkedHashMap)m;
        if (LinkedHashMap.access$000(lm)) {
            lm.modCount++;
            remove();
            addBefore(LinkedHashMap.access$100(lm));
        }
    }
    
    void recordRemoval(HashMap m) {
        remove();
    }
}
