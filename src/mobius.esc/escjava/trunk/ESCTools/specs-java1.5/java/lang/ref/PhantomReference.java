package java.lang.ref;

public class PhantomReference extends Reference {
    
    public Object get() {
        return null;
    }
    
    public PhantomReference(Object referent, ReferenceQueue q) {
        super(referent, q);
    }
}
