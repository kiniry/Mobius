package java.nio;

class ByteBufferAsIntBufferRL extends ByteBufferAsIntBufferL {
    /*synthetic*/ static final boolean $assertionsDisabled = !ByteBufferAsIntBufferRL.class.desiredAssertionStatus();
    
    ByteBufferAsIntBufferRL(ByteBuffer bb) {
        super(bb);
    }
    
    ByteBufferAsIntBufferRL(ByteBuffer bb, int mark, int pos, int lim, int cap, int off) {
        super(bb, mark, pos, lim, cap, off);
    }
    
    public IntBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 2) + offset;
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new ByteBufferAsIntBufferRL(bb, -1, 0, rem, rem, off);
    }
    
    public IntBuffer duplicate() {
        return new ByteBufferAsIntBufferRL(bb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
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
    
    public IntBuffer compact() {
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
