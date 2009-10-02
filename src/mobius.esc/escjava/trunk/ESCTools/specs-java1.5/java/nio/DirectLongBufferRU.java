package java.nio;

import sun.nio.ch.DirectBuffer;

class DirectLongBufferRU extends DirectLongBufferU implements DirectBuffer {
    /*synthetic*/ static final boolean $assertionsDisabled = !DirectLongBufferRU.class.desiredAssertionStatus();
    
    DirectLongBufferRU(DirectBuffer db, int mark, int pos, int lim, int cap, int off) {
        super(db, mark, pos, lim, cap, off);
    }
    
    public LongBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 3);
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new DirectLongBufferRU(this, -1, 0, rem, rem, off);
    }
    
    public LongBuffer duplicate() {
        return new DirectLongBufferRU(this, this.markValue(), this.position(), this.limit(), this.capacity(), 0);
    }
    
    public LongBuffer asReadOnlyBuffer() {
        return duplicate();
    }
    
    public LongBuffer put(long x) {
        throw new ReadOnlyBufferException();
    }
    
    public LongBuffer put(int i, long x) {
        throw new ReadOnlyBufferException();
    }
    
    public LongBuffer put(LongBuffer src) {
        throw new ReadOnlyBufferException();
    }
    
    public LongBuffer put(long[] src, int offset, int length) {
        throw new ReadOnlyBufferException();
    }
    
    public LongBuffer compact() {
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
