package java.nio;

import sun.misc.Unsafe;

class DirectByteBuffer$Deallocator implements Runnable {
    
    /*synthetic*/ DirectByteBuffer$Deallocator(long x0, int x1, java.nio.DirectByteBuffer$1 x2) {
        this(x0, x1);
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !DirectByteBuffer.class.desiredAssertionStatus();
    private static Unsafe unsafe = Unsafe.getUnsafe();
    private long address;
    private int capacity;
    
    private DirectByteBuffer$Deallocator(long address, int capacity) {
        
        if (!$assertionsDisabled && !(address != 0)) throw new AssertionError();
        this.address = address;
        this.capacity = capacity;
    }
    
    public void run() {
        if (address == 0) {
            return;
        }
        unsafe.freeMemory(address);
        address = 0;
        Bits.unreserveMemory(capacity);
    }
}
