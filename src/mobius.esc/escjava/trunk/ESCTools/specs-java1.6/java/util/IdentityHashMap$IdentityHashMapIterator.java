package java.util;

import java.io.*;

abstract class IdentityHashMap$IdentityHashMapIterator implements Iterator {
    
    /*synthetic*/ IdentityHashMap$IdentityHashMapIterator(IdentityHashMap x0, java.util.IdentityHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final IdentityHashMap this$0;
    
    private IdentityHashMap$IdentityHashMapIterator(/*synthetic*/ final IdentityHashMap this$0) {
        this.this$0 = this$0;
        
    }
    int index = (IdentityHashMap.access$000(this$0) != 0 ? 0 : IdentityHashMap.access$100(this$0).length);
    int expectedModCount = IdentityHashMap.access$200(this$0);
    int lastReturnedIndex = -1;
    boolean indexValid;
    Object[] traversalTable = IdentityHashMap.access$100(this$0);
    
    public boolean hasNext() {
        Object[] tab = traversalTable;
        for (int i = index; i < tab.length; i += 2) {
            Object key = tab[i];
            if (key != null) {
                index = i;
                return indexValid = true;
            }
        }
        index = tab.length;
        return false;
    }
    
    protected int nextIndex() {
        if (IdentityHashMap.access$200(this$0) != expectedModCount) throw new ConcurrentModificationException();
        if (!indexValid && !hasNext()) throw new NoSuchElementException();
        indexValid = false;
        lastReturnedIndex = index;
        index += 2;
        return lastReturnedIndex;
    }
    
    public void remove() {
        if (lastReturnedIndex == -1) throw new IllegalStateException();
        if (IdentityHashMap.access$200(this$0) != expectedModCount) throw new ConcurrentModificationException();
        expectedModCount = IdentityHashMap.access$204(this$0);
        int deletedSlot = lastReturnedIndex;
        lastReturnedIndex = -1;
        IdentityHashMap.access$010(this$0);
        index = deletedSlot;
        indexValid = false;
        Object[] tab = traversalTable;
        int len = tab.length;
        int d = deletedSlot;
        Object key = (Object)tab[d];
        tab[d] = null;
        tab[d + 1] = null;
        if (tab != IdentityHashMap.access$100(this$0)) {
            this$0.remove(key);
            expectedModCount = IdentityHashMap.access$200(this$0);
            return;
        }
        Object item;
        for (int i = IdentityHashMap.access$300(d, len); (item = tab[i]) != null; i = IdentityHashMap.access$300(i, len)) {
            int r = IdentityHashMap.access$400(item, len);
            if ((i < r && (r <= d || d <= i)) || (r <= d && d <= i)) {
                if (i < deletedSlot && d >= deletedSlot && traversalTable == IdentityHashMap.access$100(this$0)) {
                    int remaining = len - deletedSlot;
                    Object[] newTable = new Object[remaining];
                    System.arraycopy(tab, deletedSlot, newTable, 0, remaining);
                    traversalTable = newTable;
                    index = 0;
                }
                tab[d] = item;
                tab[d + 1] = tab[i + 1];
                tab[i] = null;
                tab[i + 1] = null;
                d = i;
            }
        }
    }
}
