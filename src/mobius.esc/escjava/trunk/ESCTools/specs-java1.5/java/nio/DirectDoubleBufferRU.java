package java.nio;

import sun.nio.ch.DirectBuffer;

class DirectDoubleBufferRU extends DirectDoubleBufferU implements DirectBuffer {
    /*synthetic*/ static final boolean $assertionsDisabled = !DirectDoubleBufferRU.class.desiredAssertionStatus();
    
    DirectDoubleBufferRU(DirectBuffer db, int mark, int pos, int lim, int cap, int off) {
        super(db, mark, pos, lim, cap, off);
    }
    
    public DoubleBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 3);
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new DirectDoubleBufferRU(this, -1, 0, rem, rem, off);
    }
    
    public DoubleBuffer duplicate() {
        return new DirectDoubleBufferRU(this, this.markValue(), this.position(), this.limit(), this.capacity(), 0);
    }
    
    public DoubleBuffer asReadOnlyBuffer() {
        return duplicate();
    }
    
    public DoubleBuffer put(double x) {
        throw new ReadOnlyBufferException();
    }
    
    public DoubleBuffer put(int i, double x) {
        throw new ReadOnlyBufferException();
    }
    
    public DoubleBuffer put(DoubleBuffer src) {
        throw new ReadOnlyBufferException();
    }
    
    public DoubleBuffer put(double[] src, int offset, int length) {
        throw new ReadOnlyBufferException();
    }
    
    public DoubleBuffer compact() {
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
