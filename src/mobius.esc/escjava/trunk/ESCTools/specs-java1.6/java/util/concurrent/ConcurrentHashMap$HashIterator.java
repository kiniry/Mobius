package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

abstract class ConcurrentHashMap$HashIterator {
    /*synthetic*/ final ConcurrentHashMap this$0;
    int nextSegmentIndex;
    int nextTableIndex;
    ConcurrentHashMap$HashEntry[] currentTable;
    ConcurrentHashMap$HashEntry nextEntry;
    ConcurrentHashMap$HashEntry lastReturned;
    
    ConcurrentHashMap$HashIterator(/*synthetic*/ final ConcurrentHashMap this$0) {
        this.this$0 = this$0;
        
        nextSegmentIndex = this$0.segments.length - 1;
        nextTableIndex = -1;
        advance();
    }
    
    public boolean hasMoreElements() {
        return hasNext();
    }
    
    final void advance() {
        if (nextEntry != null && (nextEntry = nextEntry.next) != null) return;
        while (nextTableIndex >= 0) {
            if ((nextEntry = (ConcurrentHashMap$HashEntry)currentTable[nextTableIndex--]) != null) return;
        }
        while (nextSegmentIndex >= 0) {
            ConcurrentHashMap$Segment seg = (ConcurrentHashMap$Segment)this$0.segments[nextSegmentIndex--];
            if (seg.count != 0) {
                currentTable = seg.table;
                for (int j = currentTable.length - 1; j >= 0; --j) {
                    if ((nextEntry = (ConcurrentHashMap$HashEntry)currentTable[j]) != null) {
                        nextTableIndex = j - 1;
                        return;
                    }
                }
            }
        }
    }
    
    public boolean hasNext() {
        return nextEntry != null;
    }
    
    ConcurrentHashMap$HashEntry nextEntry() {
        if (nextEntry == null) throw new NoSuchElementException();
        lastReturned = nextEntry;
        advance();
        return lastReturned;
    }
    
    public void remove() {
        if (lastReturned == null) throw new IllegalStateException();
        this$0.remove(lastReturned.key);
        lastReturned = null;
    }
}
