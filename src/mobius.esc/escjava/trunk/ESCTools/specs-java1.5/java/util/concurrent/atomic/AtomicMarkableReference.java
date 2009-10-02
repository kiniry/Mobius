package java.util.concurrent.atomic;

public class AtomicMarkableReference {
    {
    }
    private final AtomicReference atomicRef;
    
    public AtomicMarkableReference(Object initialRef, boolean initialMark) {
        
        atomicRef = new AtomicReference(new AtomicMarkableReference$ReferenceBooleanPair(initialRef, initialMark));
    }
    
    public Object getReference() {
        return AtomicMarkableReference.ReferenceBooleanPair.access$000((AtomicMarkableReference$ReferenceBooleanPair)atomicRef.get());
    }
    
    public boolean isMarked() {
        return AtomicMarkableReference.ReferenceBooleanPair.access$100((AtomicMarkableReference$ReferenceBooleanPair)atomicRef.get());
    }
    
    public Object get(boolean[] markHolder) {
        AtomicMarkableReference$ReferenceBooleanPair p = (AtomicMarkableReference$ReferenceBooleanPair)atomicRef.get();
        markHolder[0] = AtomicMarkableReference.ReferenceBooleanPair.access$100(p);
        return AtomicMarkableReference.ReferenceBooleanPair.access$000(p);
    }
    
    public boolean weakCompareAndSet(Object expectedReference, Object newReference, boolean expectedMark, boolean newMark) {
        AtomicMarkableReference$ReferenceBooleanPair current = (AtomicMarkableReference$ReferenceBooleanPair)atomicRef.get();
        return expectedReference == AtomicMarkableReference.ReferenceBooleanPair.access$000(current) && expectedMark == AtomicMarkableReference.ReferenceBooleanPair.access$100(current) && ((newReference == AtomicMarkableReference.ReferenceBooleanPair.access$000(current) && newMark == AtomicMarkableReference.ReferenceBooleanPair.access$100(current)) || atomicRef.weakCompareAndSet(current, new AtomicMarkableReference$ReferenceBooleanPair(newReference, newMark)));
    }
    
    public boolean compareAndSet(Object expectedReference, Object newReference, boolean expectedMark, boolean newMark) {
        AtomicMarkableReference$ReferenceBooleanPair current = (AtomicMarkableReference$ReferenceBooleanPair)atomicRef.get();
        return expectedReference == AtomicMarkableReference.ReferenceBooleanPair.access$000(current) && expectedMark == AtomicMarkableReference.ReferenceBooleanPair.access$100(current) && ((newReference == AtomicMarkableReference.ReferenceBooleanPair.access$000(current) && newMark == AtomicMarkableReference.ReferenceBooleanPair.access$100(current)) || atomicRef.compareAndSet(current, new AtomicMarkableReference$ReferenceBooleanPair(newReference, newMark)));
    }
    
    public void set(Object newReference, boolean newMark) {
        AtomicMarkableReference$ReferenceBooleanPair current = (AtomicMarkableReference$ReferenceBooleanPair)atomicRef.get();
        if (newReference != AtomicMarkableReference.ReferenceBooleanPair.access$000(current) || newMark != AtomicMarkableReference.ReferenceBooleanPair.access$100(current)) atomicRef.set(new AtomicMarkableReference$ReferenceBooleanPair(newReference, newMark));
    }
    
    public boolean attemptMark(Object expectedReference, boolean newMark) {
        AtomicMarkableReference$ReferenceBooleanPair current = (AtomicMarkableReference$ReferenceBooleanPair)atomicRef.get();
        return expectedReference == AtomicMarkableReference.ReferenceBooleanPair.access$000(current) && (newMark == AtomicMarkableReference.ReferenceBooleanPair.access$100(current) || atomicRef.compareAndSet(current, new AtomicMarkableReference$ReferenceBooleanPair(expectedReference, newMark)));
    }
}
