package java.lang.ref;

public class SoftReference extends Reference {
    private static long clock;
    private long timestamp;
    
    public SoftReference(Object referent) {
        super(referent);
        this.timestamp = clock;
    }
    
    public SoftReference(Object referent, ReferenceQueue q) {
        super(referent, q);
        this.timestamp = clock;
    }
    
    public Object get() {
        Object o = super.get();
        if (o != null) this.timestamp = clock;
        return o;
    }
}
