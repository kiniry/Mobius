package java.util.concurrent.atomic;

class AtomicStampedReference$ReferenceIntegerPair {
    
    /*synthetic*/ static int access$100(AtomicStampedReference$ReferenceIntegerPair x0) {
        return x0.integer;
    }
    
    /*synthetic*/ static Object access$000(AtomicStampedReference$ReferenceIntegerPair x0) {
        return x0.reference;
    }
    private final Object reference;
    private final int integer;
    
    AtomicStampedReference$ReferenceIntegerPair(Object r, int i) {
        
        reference = r;
        integer = i;
    }
}
