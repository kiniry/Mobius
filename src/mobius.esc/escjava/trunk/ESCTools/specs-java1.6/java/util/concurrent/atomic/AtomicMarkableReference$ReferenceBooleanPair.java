package java.util.concurrent.atomic;

class AtomicMarkableReference$ReferenceBooleanPair {
    
    /*synthetic*/ static boolean access$100(AtomicMarkableReference$ReferenceBooleanPair x0) {
        return x0.bit;
    }
    
    /*synthetic*/ static Object access$000(AtomicMarkableReference$ReferenceBooleanPair x0) {
        return x0.reference;
    }
    private final Object reference;
    private final boolean bit;
    
    AtomicMarkableReference$ReferenceBooleanPair(Object r, boolean i) {
        
        reference = r;
        bit = i;
    }
}
