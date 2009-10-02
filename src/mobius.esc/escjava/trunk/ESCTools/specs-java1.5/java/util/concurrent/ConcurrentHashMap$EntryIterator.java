package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

final class ConcurrentHashMap$EntryIterator extends ConcurrentHashMap$HashIterator implements Map$Entry, Iterator {
    /*synthetic*/ final ConcurrentHashMap this$0;
    
    ConcurrentHashMap$EntryIterator(/*synthetic*/ final ConcurrentHashMap this$0) {
        super(this.this$0 = this$0);
    }
    
    public Map$Entry next() {
        nextEntry();
        return this;
    }
    
    public Object getKey() {
        if (lastReturned == null) throw new IllegalStateException("Entry was removed");
        return lastReturned.key;
    }
    
    public Object getValue() {
        if (lastReturned == null) throw new IllegalStateException("Entry was removed");
        return this$0.get(lastReturned.key);
    }
    
    public Object setValue(Object value) {
        if (lastReturned == null) throw new IllegalStateException("Entry was removed");
        return this$0.put(lastReturned.key, value);
    }
    
    public boolean equals(Object o) {
        if (lastReturned == null) return super.equals(o);
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry e = (Map$Entry)(Map$Entry)o;
        return eq(getKey(), e.getKey()) && eq(getValue(), e.getValue());
    }
    
    public int hashCode() {
        if (lastReturned == null) return super.hashCode();
        Object k = getKey();
        Object v = getValue();
        return ((k == null) ? 0 : k.hashCode()) ^ ((v == null) ? 0 : v.hashCode());
    }
    
    public String toString() {
        if (lastReturned == null) return super.toString(); else return getKey() + "=" + getValue();
    }
    
    boolean eq(Object o1, Object o2) {
        return (o1 == null ? o2 == null : o1.equals(o2));
    }
    
    /*synthetic public Object next() {
        return this.next();
    }*/
}
