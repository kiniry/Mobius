package java.nio;

import sun.nio.ch.DirectBuffer;

class DirectIntBufferRU extends DirectIntBufferU implements DirectBuffer {
    /*synthetic*/ static final boolean $assertionsDisabled = !DirectIntBufferRU.class.desiredAssertionStatus();
    
    DirectIntBufferRU(DirectBuffer db, int mark, int pos, int lim, int cap, int off) {
        super(db, mark, pos, lim, cap, off);
    }
    
    public IntBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 2);
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new DirectIntBufferRU(this, -1, 0, rem, rem, off);
    }
    
    public IntBuffer duplicate() {
        return new DirectIntBufferRU(this, this.markValue(), this.position(), this.limit(), this.capacity(), 0);
    }
    
    public IntBuffer asReadOnlyBuffer() {
        return duplicate();
    }
    
    public IntBuffer put(int x) {
        throw new ReadOnlyBufferException();
    }
    
    public IntBuffer put(int i, int x) {
        throw new ReadOnlyBufferException();
    }
    
    public IntBuffer put(IntBuffer src) {
        throw new ReadOnlyBufferException();
    }
    
    public IntBuffer put(int[] src, int offset, int length) {
        throw new ReadOnlyBufferException();
    }
    
    public IntBuffer compact() {
        throw new ReadOnlyBufferException();
    }
    
    public boolean isDirect() {
        return true;
    }
    
    public boolean isReadOnly() {
        return true;
    }
    
    public ByteOrder order() {
        return ((ByteOrder.nativeOrder() != ByteOrder.BIG_ENDIAN) ? ByteOrder.LITTLE_ENDIAN : ByteOrder.BIG_ENDIAN);
    }
}
