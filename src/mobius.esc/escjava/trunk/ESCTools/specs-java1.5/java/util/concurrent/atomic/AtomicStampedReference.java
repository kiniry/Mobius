package java.util.concurrent.atomic;

public class AtomicStampedReference {
    {
    }
    private final AtomicReference atomicRef;
    
    public AtomicStampedReference(Object initialRef, int initialStamp) {
        
        atomicRef = new AtomicReference(new AtomicStampedReference$ReferenceIntegerPair(initialRef, initialStamp));
    }
    
    public Object getReference() {
        return AtomicStampedReference.ReferenceIntegerPair.access$000((AtomicStampedReference$ReferenceIntegerPair)atomicRef.get());
    }
    
    public int getStamp() {
        return AtomicStampedReference.ReferenceIntegerPair.access$100((AtomicStampedReference$ReferenceIntegerPair)atomicRef.get());
    }
    
    public Object get(int[] stampHolder) {
        AtomicStampedReference$ReferenceIntegerPair p = (AtomicStampedReference$ReferenceIntegerPair)atomicRef.get();
        stampHolder[0] = AtomicStampedReference.ReferenceIntegerPair.access$100(p);
        return AtomicStampedReference.ReferenceIntegerPair.access$000(p);
    }
    
    public boolean weakCompareAndSet(Object expectedReference, Object newReference, int expectedStamp, int newStamp) {
        AtomicStampedReference$ReferenceIntegerPair current = (AtomicStampedReference$ReferenceIntegerPair)atomicRef.get();
        return expectedReference == AtomicStampedReference.ReferenceIntegerPair.access$000(current) && expectedStamp == AtomicStampedReference.ReferenceIntegerPair.access$100(current) && ((newReference == AtomicStampedReference.ReferenceIntegerPair.access$000(current) && newStamp == AtomicStampedReference.ReferenceIntegerPair.access$100(current)) || atomicRef.weakCompareAndSet(current, new AtomicStampedReference$ReferenceIntegerPair(newReference, newStamp)));
    }
    
    public boolean compareAndSet(Object expectedReference, Object newReference, int expectedStamp, int newStamp) {
        AtomicStampedReference$ReferenceIntegerPair current = (AtomicStampedReference$ReferenceIntegerPair)atomicRef.get();
        return expectedReference == AtomicStampedReference.ReferenceIntegerPair.access$000(current) && expectedStamp == AtomicStampedReference.ReferenceIntegerPair.access$100(current) && ((newReference == AtomicStampedReference.ReferenceIntegerPair.access$000(current) && newStamp == AtomicStampedReference.ReferenceIntegerPair.access$100(current)) || atomicRef.compareAndSet(current, new AtomicStampedReference$ReferenceIntegerPair(newReference, newStamp)));
    }
    
    public void set(Object newReference, int newStamp) {
        AtomicStampedReference$ReferenceIntegerPair current = (AtomicStampedReference$ReferenceIntegerPair)atomicRef.get();
        if (newReference != AtomicStampedReference.ReferenceIntegerPair.access$000(current) || newStamp != AtomicStampedReference.ReferenceIntegerPair.access$100(current)) atomicRef.set(new AtomicStampedReference$ReferenceIntegerPair(newReference, newStamp));
    }
    
    public boolean attemptStamp(Object expectedReference, int newStamp) {
        AtomicStampedReference$ReferenceIntegerPair current = (AtomicStampedReference$ReferenceIntegerPair)atomicRef.get();
        return expectedReference == AtomicStampedReference.ReferenceIntegerPair.access$000(current) && (newStamp == AtomicStampedReference.ReferenceIntegerPair.access$100(current) || atomicRef.compareAndSet(current, new AtomicStampedReference$ReferenceIntegerPair(expectedReference, newStamp)));
    }
}
