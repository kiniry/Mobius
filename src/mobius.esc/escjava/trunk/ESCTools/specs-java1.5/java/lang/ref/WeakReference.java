package java.lang.ref;

public class WeakReference extends Reference {
    
    public WeakReference(Object referent) {
        super(referent);
    }
    
    public WeakReference(Object referent, ReferenceQueue q) {
        super(referent, q);
    }
}
