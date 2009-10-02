package java.util;

abstract class WeakHashMap$HashIterator implements Iterator {
    /*synthetic*/ final WeakHashMap this$0;
    int index;
    WeakHashMap$Entry entry = null;
    WeakHashMap$Entry lastReturned = null;
    int expectedModCount = WeakHashMap.access$400(this$0);
    Object nextKey = null;
    Object currentKey = null;
    
    WeakHashMap$HashIterator(/*synthetic*/ final WeakHashMap this$0) {
        this.this$0 = this$0;
        
        index = (this$0.size() != 0 ? WeakHashMap.access$500(this$0).length : 0);
    }
    
    public boolean hasNext() {
        WeakHashMap$Entry[] t = WeakHashMap.access$500(this$0);
        while (nextKey == null) {
            WeakHashMap$Entry e = entry;
            int i = index;
            while (e == null && i > 0) e = t[--i];
            entry = e;
            index = i;
            if (e == null) {
                currentKey = null;
                return false;
            }
            nextKey = e.get();
            if (nextKey == null) entry = WeakHashMap.Entry.access$100(entry);
        }
        return true;
    }
    
    protected WeakHashMap$Entry nextEntry() {
        if (WeakHashMap.access$400(this$0) != expectedModCount) throw new ConcurrentModificationException();
        if (nextKey == null && !hasNext()) throw new NoSuchElementException();
        lastReturned = entry;
        entry = WeakHashMap.Entry.access$100(entry);
        currentKey = nextKey;
        nextKey = null;
        return lastReturned;
    }
    
    public void remove() {
        if (lastReturned == null) throw new IllegalStateException();
        if (WeakHashMap.access$400(this$0) != expectedModCount) throw new ConcurrentModificationException();
        this$0.remove(currentKey);
        expectedModCount = WeakHashMap.access$400(this$0);
        lastReturned = null;
        currentKey = null;
    }
}
