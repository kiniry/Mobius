package javax.print;

class MimeType$ParameterMapEntry implements Map$Entry {
    /*synthetic*/ final MimeType this$0;
    private int myIndex;
    
    public MimeType$ParameterMapEntry(/*synthetic*/ final MimeType this$0, int theIndex) {
        this.this$0 = this$0;
        
        myIndex = theIndex;
    }
    
    public Object getKey() {
        return MimeType.access$000(this$0)[myIndex];
    }
    
    public Object getValue() {
        return MimeType.access$000(this$0)[myIndex + 1];
    }
    
    public Object setValue(Object value) {
        throw new UnsupportedOperationException();
    }
    
    public boolean equals(Object o) {
        return (o != null && o instanceof Map$Entry && getKey().equals(((Map$Entry)(Map$Entry)o).getKey()) && getValue().equals(((Map$Entry)(Map$Entry)o).getValue()));
    }
    
    public int hashCode() {
        return getKey().hashCode() ^ getValue().hashCode();
    }
}
