package java.nio;

class ByteBufferAsFloatBufferL extends FloatBuffer {
    /*synthetic*/ static final boolean $assertionsDisabled = !ByteBufferAsFloatBufferL.class.desiredAssertionStatus();
    protected final ByteBuffer bb;
    protected final int offset;
    
    ByteBufferAsFloatBufferL(ByteBuffer bb) {
        super(-1, 0, bb.remaining() >> 2, bb.remaining() >> 2);
        this.bb = bb;
        int cap = this.capacity();
        this.limit(cap);
        int pos = this.position();
        if (!$assertionsDisabled && !(pos <= cap)) throw new AssertionError();
        offset = pos;
    }
    
    ByteBufferAsFloatBufferL(ByteBuffer bb, int mark, int pos, int lim, int cap, int off) {
        super(mark, pos, lim, cap);
        this.bb = bb;
        offset = off;
    }
    
    public FloatBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 2) + offset;
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new ByteBufferAsFloatBufferL(bb, -1, 0, rem, rem, off);
    }
    
    public FloatBuffer duplicate() {
        return new ByteBufferAsFloatBufferL(bb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    public FloatBuffer asReadOnlyBuffer() {
        return new ByteBufferAsFloatBufferRL(bb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    protected int ix(int i) {
        return (i << 2) + offset;
    }
    
    public float get() {
        return Bits.getFloatL(bb, ix(nextGetIndex()));
    }
    
    public float get(int i) {
        return Bits.getFloatL(bb, ix(checkIndex(i)));
    }
    
    public FloatBuffer put(float x) {
        Bits.putFloatL(bb, ix(nextPutIndex()), x);
        return this;
    }
    
    public FloatBuffer put(int i, float x) {
        Bits.putFloatL(bb, ix(checkIndex(i)), x);
        return this;
    }
    
    public FloatBuffer compact() {
        int pos = position();
        int lim = limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        ByteBuffer db = bb.duplicate();
        db.limit(ix(lim));
        db.position(ix(0));
        ByteBuffer sb = db.slice();
        sb.position(pos << 2);
        sb.compact();
        position(rem);
        limit(capacity());
        return this;
    }
    
    public boolean isDirect() {
        return bb.isDirect();
    }
    
    public boolean isReadOnly() {
        return false;
    }
    
    public ByteOrder order() {
        return ByteOrder.LITTLE_ENDIAN;
    }
}
