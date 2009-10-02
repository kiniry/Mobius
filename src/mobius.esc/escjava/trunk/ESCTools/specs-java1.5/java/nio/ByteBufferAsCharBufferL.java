package java.nio;

class ByteBufferAsCharBufferL extends CharBuffer {
    /*synthetic*/ static final boolean $assertionsDisabled = !ByteBufferAsCharBufferL.class.desiredAssertionStatus();
    protected final ByteBuffer bb;
    protected final int offset;
    
    ByteBufferAsCharBufferL(ByteBuffer bb) {
        super(-1, 0, bb.remaining() >> 1, bb.remaining() >> 1);
        this.bb = bb;
        int cap = this.capacity();
        this.limit(cap);
        int pos = this.position();
        if (!$assertionsDisabled && !(pos <= cap)) throw new AssertionError();
        offset = pos;
    }
    
    ByteBufferAsCharBufferL(ByteBuffer bb, int mark, int pos, int lim, int cap, int off) {
        super(mark, pos, lim, cap);
        this.bb = bb;
        offset = off;
    }
    
    public CharBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 1) + offset;
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new ByteBufferAsCharBufferL(bb, -1, 0, rem, rem, off);
    }
    
    public CharBuffer duplicate() {
        return new ByteBufferAsCharBufferL(bb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    public CharBuffer asReadOnlyBuffer() {
        return new ByteBufferAsCharBufferRL(bb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    protected int ix(int i) {
        return (i << 1) + offset;
    }
    
    public char get() {
        return Bits.getCharL(bb, ix(nextGetIndex()));
    }
    
    public char get(int i) {
        return Bits.getCharL(bb, ix(checkIndex(i)));
    }
    
    public CharBuffer put(char x) {
        Bits.putCharL(bb, ix(nextPutIndex()), x);
        return this;
    }
    
    public CharBuffer put(int i, char x) {
        Bits.putCharL(bb, ix(checkIndex(i)), x);
        return this;
    }
    
    public CharBuffer compact() {
        int pos = position();
        int lim = limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        ByteBuffer db = bb.duplicate();
        db.limit(ix(lim));
        db.position(ix(0));
        ByteBuffer sb = db.slice();
        sb.position(pos << 1);
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
    
    public String toString(int start, int end) {
        if ((end > limit()) || (start > end)) throw new IndexOutOfBoundsException();
        try {
            int len = end - start;
            char[] ca = new char[len];
            CharBuffer cb = CharBuffer.wrap(ca);
            CharBuffer db = this.duplicate();
            db.position(start);
            db.limit(end);
            cb.put(db);
            return new String(ca);
        } catch (StringIndexOutOfBoundsException x) {
            throw new IndexOutOfBoundsException();
        }
    }
    
    public CharSequence subSequence(int start, int end) {
        int pos = position();
        int lim = limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        pos = (pos <= lim ? pos : lim);
        int len = lim - pos;
        if ((start < 0) || (end > len) || (start > end)) throw new IndexOutOfBoundsException();
        int sublen = end - start;
        int off = offset + ((pos + start) << 1);
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new ByteBufferAsCharBufferL(bb, -1, 0, sublen, sublen, off);
    }
    
    public ByteOrder order() {
        return ByteOrder.LITTLE_ENDIAN;
    }
}
