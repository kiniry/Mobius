package java.lang.ref;

class FinalReference extends Reference {
    
    public FinalReference(Object referent, ReferenceQueue q) {
        super(referent, q);
    }
}
