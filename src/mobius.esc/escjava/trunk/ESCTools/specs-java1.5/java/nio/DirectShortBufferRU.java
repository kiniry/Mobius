package java.nio;

import sun.nio.ch.DirectBuffer;

class DirectShortBufferRU extends DirectShortBufferU implements DirectBuffer {
    /*synthetic*/ static final boolean $assertionsDisabled = !DirectShortBufferRU.class.desiredAssertionStatus();
    
    DirectShortBufferRU(DirectBuffer db, int mark, int pos, int lim, int cap, int off) {
        super(db, mark, pos, lim, cap, off);
    }
    
    public ShortBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 1);
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new DirectShortBufferRU(this, -1, 0, rem, rem, off);
    }
    
    public ShortBuffer duplicate() {
        return new DirectShortBufferRU(this, this.markValue(), this.position(), this.limit(), this.capacity(), 0);
    }
    
    public ShortBuffer asReadOnlyBuffer() {
        return duplicate();
    }
    
    public ShortBuffer put(short x) {
        throw new ReadOnlyBufferException();
    }
    
    public ShortBuffer put(int i, short x) {
        throw new ReadOnlyBufferException();
    }
    
    public ShortBuffer put(ShortBuffer src) {
        throw new ReadOnlyBufferException();
    }
    
    public ShortBuffer put(short[] src, int offset, int length) {
        throw new ReadOnlyBufferException();
    }
    
    public ShortBuffer compact() {
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
