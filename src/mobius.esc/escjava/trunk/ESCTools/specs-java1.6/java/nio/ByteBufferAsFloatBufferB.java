package java.nio;

class ByteBufferAsFloatBufferB extends FloatBuffer {
    /*synthetic*/ static final boolean $assertionsDisabled = !ByteBufferAsFloatBufferB.class.desiredAssertionStatus();
    protected final ByteBuffer bb;
    protected final int offset;
    
    ByteBufferAsFloatBufferB(ByteBuffer bb) {
        super(-1, 0, bb.remaining() >> 2, bb.remaining() >> 2);
        this.bb = bb;
        int cap = this.capacity();
        this.limit(cap);
        int pos = this.position();
        if (!$assertionsDisabled && !(pos <= cap)) throw new AssertionError();
        offset = pos;
    }
    
    ByteBufferAsFloatBufferB(ByteBuffer bb, int mark, int pos, int lim, int cap, int off) {
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
        return new ByteBufferAsFloatBufferB(bb, -1, 0, rem, rem, off);
    }
    
    public FloatBuffer duplicate() {
        return new ByteBufferAsFloatBufferB(bb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    public FloatBuffer asReadOnlyBuffer() {
        return new ByteBufferAsFloatBufferRB(bb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    protected int ix(int i) {
        return (i << 2) + offset;
    }
    
    public float get() {
        return Bits.getFloatB(bb, ix(nextGetIndex()));
    }
    
    public float get(int i) {
        return Bits.getFloatB(bb, ix(checkIndex(i)));
    }
    
    public FloatBuffer put(float x) {
        Bits.putFloatB(bb, ix(nextPutIndex()), x);
        return this;
    }
    
    public FloatBuffer put(int i, float x) {
        Bits.putFloatB(bb, ix(checkIndex(i)), x);
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
        return ByteOrder.BIG_ENDIAN;
    }
}
