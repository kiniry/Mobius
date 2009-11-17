package java.nio;

class ByteBufferAsShortBufferRL extends ByteBufferAsShortBufferL {
    /*synthetic*/ static final boolean $assertionsDisabled = !ByteBufferAsShortBufferRL.class.desiredAssertionStatus();
    
    ByteBufferAsShortBufferRL(ByteBuffer bb) {
        super(bb);
    }
    
    ByteBufferAsShortBufferRL(ByteBuffer bb, int mark, int pos, int lim, int cap, int off) {
        super(bb, mark, pos, lim, cap, off);
    }
    
    public ShortBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 1) + offset;
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new ByteBufferAsShortBufferRL(bb, -1, 0, rem, rem, off);
    }
    
    public ShortBuffer duplicate() {
        return new ByteBufferAsShortBufferRL(bb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
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
    
    public ShortBuffer compact() {
        throw new ReadOnlyBufferException();
    }
    
    public boolean isDirect() {
        return bb.isDirect();
    }
    
    public boolean isReadOnly() {
        return true;
    }
    
    public ByteOrder order() {
        return ByteOrder.LITTLE_ENDIAN;
    }
}
