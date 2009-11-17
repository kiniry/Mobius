package java.util;

import java.util.Map.Entry;

class EnumMap$EntrySet extends AbstractSet {
    
    /*synthetic*/ EnumMap$EntrySet(EnumMap x0, java.util.EnumMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final EnumMap this$0;
    
    private EnumMap$EntrySet(/*synthetic*/ final EnumMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new EnumMap$EntryIterator(this$0, null);
    }
    
    public boolean contains(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry entry = (Map$Entry)(Map$Entry)o;
        return EnumMap.access$900(this$0, entry.getKey(), entry.getValue());
    }
    
    public boolean remove(Object o) {
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry entry = (Map$Entry)(Map$Entry)o;
        return EnumMap.access$1000(this$0, entry.getKey(), entry.getValue());
    }
    
    public int size() {
        return EnumMap.access$200(this$0);
    }
    
    public void clear() {
        this$0.clear();
    }
    
    public Object[] toArray() {
        return fillEntryArray(new Object[EnumMap.access$200(this$0)]);
    }
    
    public Object[] toArray(Object[] a) {
        int size = size();
        if (a.length < size) a = (Object[])(Object[])java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), size);
        if (a.length > size) a[size] = null;
        return (Object[])fillEntryArray(a);
    }
    
    private Object[] fillEntryArray(Object[] a) {
        int j = 0;
        for (int i = 0; i < EnumMap.access$600(this$0).length; i++) if (EnumMap.access$600(this$0)[i] != null) a[j++] = new AbstractMap$SimpleEntry(EnumMap.access$1100(this$0)[i], EnumMap.access$1200(this$0, EnumMap.access$600(this$0)[i]));
        return a;
    }
}
