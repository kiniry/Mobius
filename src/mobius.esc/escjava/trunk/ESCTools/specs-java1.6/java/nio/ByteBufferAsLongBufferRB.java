package java.nio;

class ByteBufferAsLongBufferRB extends ByteBufferAsLongBufferB {
    /*synthetic*/ static final boolean $assertionsDisabled = !ByteBufferAsLongBufferRB.class.desiredAssertionStatus();
    
    ByteBufferAsLongBufferRB(ByteBuffer bb) {
        super(bb);
    }
    
    ByteBufferAsLongBufferRB(ByteBuffer bb, int mark, int pos, int lim, int cap, int off) {
        super(bb, mark, pos, lim, cap, off);
    }
    
    public LongBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 3) + offset;
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new ByteBufferAsLongBufferRB(bb, -1, 0, rem, rem, off);
    }
    
    public LongBuffer duplicate() {
        return new ByteBufferAsLongBufferRB(bb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
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
    
    public LongBuffer compact() {
        throw new ReadOnlyBufferException();
    }
    
    public boolean isDirect() {
        return bb.isDirect();
    }
    
    public boolean isReadOnly() {
        return true;
    }
    
    public ByteOrder order() {
        return ByteOrder.BIG_ENDIAN;
    }
}
