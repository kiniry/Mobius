package java.util;

import java.util.Map.Entry;

class EnumMap$EntryIterator extends EnumMap$EnumMapIterator implements Map$Entry {
    
    /*synthetic*/ EnumMap$EntryIterator(EnumMap x0, java.util.EnumMap$1 x1) {
        this(x0);
    }
    /*synthetic*/ final EnumMap this$0;
    
    private EnumMap$EntryIterator(/*synthetic*/ final EnumMap this$0) {
        super( this.this$0 = this$0, null);
    }
    
    public Map$Entry next() {
        if (!hasNext()) throw new NoSuchElementException();
        lastReturnedIndex = index++;
        return this;
    }
    
    public Enum getKey() {
        checkLastReturnedIndexForEntryUse();
        return EnumMap.access$1100(this$0)[lastReturnedIndex];
    }
    
    public Object getValue() {
        checkLastReturnedIndexForEntryUse();
        return EnumMap.access$1200(this$0, EnumMap.access$600(this$0)[lastReturnedIndex]);
    }
    
    public Object setValue(Object value) {
        checkLastReturnedIndexForEntryUse();
        Object oldValue = EnumMap.access$1200(this$0, EnumMap.access$600(this$0)[lastReturnedIndex]);
        EnumMap.access$600(this$0)[lastReturnedIndex] = EnumMap.access$500(this$0, value);
        return oldValue;
    }
    
    public boolean equals(Object o) {
        if (lastReturnedIndex < 0) return o == this;
        if (!(o instanceof Map$Entry)) return false;
        Map$Entry e = (Map$Entry)(Map$Entry)o;
        Object ourValue = EnumMap.access$1200(this$0, EnumMap.access$600(this$0)[lastReturnedIndex]);
        Object hisValue = e.getValue();
        return e.getKey() == EnumMap.access$1100(this$0)[lastReturnedIndex] && (ourValue == hisValue || (ourValue != null && ourValue.equals(hisValue)));
    }
    
    public int hashCode() {
        if (lastReturnedIndex < 0) return super.hashCode();
        Object value = EnumMap.access$600(this$0)[lastReturnedIndex];
        return EnumMap.access$1100(this$0)[lastReturnedIndex].hashCode() ^ (value == EnumMap.access$1400() ? 0 : value.hashCode());
    }
    
    public String toString() {
        if (lastReturnedIndex < 0) return super.toString();
        return EnumMap.access$1100(this$0)[lastReturnedIndex] + "=" + EnumMap.access$1200(this$0, EnumMap.access$600(this$0)[lastReturnedIndex]);
    }
    
    private void checkLastReturnedIndexForEntryUse() {
        if (lastReturnedIndex < 0) throw new IllegalStateException("Entry was removed");
    }
    
    /*synthetic public Object next() {
        return this.next();
    }*/
    
    /*synthetic public Object getKey() {
        return this.getKey();
    } */
}
