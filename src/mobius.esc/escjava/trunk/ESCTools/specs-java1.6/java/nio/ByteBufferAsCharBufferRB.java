package java.nio;

class ByteBufferAsCharBufferRB extends ByteBufferAsCharBufferB {
    /*synthetic*/ static final boolean $assertionsDisabled = !ByteBufferAsCharBufferRB.class.desiredAssertionStatus();
    
    ByteBufferAsCharBufferRB(ByteBuffer bb) {
        super(bb);
    }
    
    ByteBufferAsCharBufferRB(ByteBuffer bb, int mark, int pos, int lim, int cap, int off) {
        super(bb, mark, pos, lim, cap, off);
    }
    
    public CharBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 1) + offset;
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new ByteBufferAsCharBufferRB(bb, -1, 0, rem, rem, off);
    }
    
    public CharBuffer duplicate() {
        return new ByteBufferAsCharBufferRB(bb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    public CharBuffer asReadOnlyBuffer() {
        return duplicate();
    }
    
    public CharBuffer put(char x) {
        throw new ReadOnlyBufferException();
    }
    
    public CharBuffer put(int i, char x) {
        throw new ReadOnlyBufferException();
    }
    
    public CharBuffer compact() {
        throw new ReadOnlyBufferException();
    }
    
    public boolean isDirect() {
        return bb.isDirect();
    }
    
    public boolean isReadOnly() {
        return true;
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
        return new ByteBufferAsCharBufferRB(bb, -1, 0, sublen, sublen, off);
    }
    
    public ByteOrder order() {
        return ByteOrder.BIG_ENDIAN;
    }
}
