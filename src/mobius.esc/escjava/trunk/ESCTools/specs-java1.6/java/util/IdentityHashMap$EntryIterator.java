package java.util;

import java.io.*;

class IdentityHashMap$EntryIterator extends IdentityHashMap$IdentityHashMapIterator implements Map$Entry {
    
    /*synthetic*/ IdentityHashMap$EntryIterator(IdentityHashMap x0, java.util.IdentityHashMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final IdentityHashMap this$0;
    
    private IdentityHashMap$EntryIterator(/*synthetic*/ final IdentityHashMap this$0) {
        super( this.this$0 = this$0, null);
    }
    
    public Map$Entry next() {
        nextIndex();
        return this;
    }
    
    public Object getKey() {
        if (lastReturnedIndex < 0) throw new IllegalStateException("Entry was removed");
        return (Object)IdentityHashMap.access$600(traversalTable[lastReturnedIndex]);
    }
    
    public Object getValue() {
        if (lastReturnedIndex < 0) throw new IllegalStateException("Entry was removed");
        return (Object)traversalTable[lastReturnedIndex + 1];
    }
    
    public Object setValue(Object value) {
        if (lastReturnedIndex < 0) throw new IllegalStateException("Entry was removed");
        Object oldValue = (Object)traversalTable[lastReturnedIndex + 1];
        traversalTable[lastReturnedIndex + 1] = value;
        if (traversalTable != IdentityHashMap.access$100(this$0)) this$0.put((Object)traversalTable[lastReturnedIndex], value);
        return oldValue;
    }
    
    public boolean equals(Object o) {
        if (lastReturnedIndex < 0) return super.equals(o);
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry e = (Map$Entry)(Map$Entry)o;
        return e.getKey() == getKey() && e.getValue() == getValue();
    }
    
    public int hashCode() {
        if (lastReturnedIndex < 0) return super.hashCode();
        return System.identityHashCode(getKey()) ^ System.identityHashCode(getValue());
    }
    
    public String toString() {
        if (lastReturnedIndex < 0) return super.toString();
        return getKey() + "=" + getValue();
    }
    
    /*synthetic public Object next() {
        return this.next();
    }*/
}
