package java.nio;

class ByteBufferAsDoubleBufferL extends DoubleBuffer {
    /*synthetic*/ static final boolean $assertionsDisabled = !ByteBufferAsDoubleBufferL.class.desiredAssertionStatus();
    protected final ByteBuffer bb;
    protected final int offset;
    
    ByteBufferAsDoubleBufferL(ByteBuffer bb) {
        super(-1, 0, bb.remaining() >> 3, bb.remaining() >> 3);
        this.bb = bb;
        int cap = this.capacity();
        this.limit(cap);
        int pos = this.position();
        if (!$assertionsDisabled && !(pos <= cap)) throw new AssertionError();
        offset = pos;
    }
    
    ByteBufferAsDoubleBufferL(ByteBuffer bb, int mark, int pos, int lim, int cap, int off) {
        super(mark, pos, lim, cap);
        this.bb = bb;
        offset = off;
    }
    
    public DoubleBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 3) + offset;
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new ByteBufferAsDoubleBufferL(bb, -1, 0, rem, rem, off);
    }
    
    public DoubleBuffer duplicate() {
        return new ByteBufferAsDoubleBufferL(bb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    public DoubleBuffer asReadOnlyBuffer() {
        return new ByteBufferAsDoubleBufferRL(bb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    protected int ix(int i) {
        return (i << 3) + offset;
    }
    
    public double get() {
        return Bits.getDoubleL(bb, ix(nextGetIndex()));
    }
    
    public double get(int i) {
        return Bits.getDoubleL(bb, ix(checkIndex(i)));
    }
    
    public DoubleBuffer put(double x) {
        Bits.putDoubleL(bb, ix(nextPutIndex()), x);
        return this;
    }
    
    public DoubleBuffer put(int i, double x) {
        Bits.putDoubleL(bb, ix(checkIndex(i)), x);
        return this;
    }
    
    public DoubleBuffer compact() {
        int pos = position();
        int lim = limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        ByteBuffer db = bb.duplicate();
        db.limit(ix(lim));
        db.position(ix(0));
        ByteBuffer sb = db.slice();
        sb.position(pos << 3);
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
