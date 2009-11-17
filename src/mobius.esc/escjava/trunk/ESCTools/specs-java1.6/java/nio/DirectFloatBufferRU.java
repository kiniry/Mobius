package java.nio;

import sun.nio.ch.DirectBuffer;

class DirectFloatBufferRU extends DirectFloatBufferU implements DirectBuffer {
    /*synthetic*/ static final boolean $assertionsDisabled = !DirectFloatBufferRU.class.desiredAssertionStatus();
    
    DirectFloatBufferRU(DirectBuffer db, int mark, int pos, int lim, int cap, int off) {
        super(db, mark, pos, lim, cap, off);
    }
    
    public FloatBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 2);
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new DirectFloatBufferRU(this, -1, 0, rem, rem, off);
    }
    
    public FloatBuffer duplicate() {
        return new DirectFloatBufferRU(this, this.markValue(), this.position(), this.limit(), this.capacity(), 0);
    }
    
    public FloatBuffer asReadOnlyBuffer() {
        return duplicate();
    }
    
    public FloatBuffer put(float x) {
        throw new ReadOnlyBufferException();
    }
    
    public FloatBuffer put(int i, float x) {
        throw new ReadOnlyBufferException();
    }
    
    public FloatBuffer put(FloatBuffer src) {
        throw new ReadOnlyBufferException();
    }
    
    public FloatBuffer put(float[] src, int offset, int length) {
        throw new ReadOnlyBufferException();
    }
    
    public FloatBuffer compact() {
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
