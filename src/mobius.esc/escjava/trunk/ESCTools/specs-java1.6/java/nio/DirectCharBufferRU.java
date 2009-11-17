package java.nio;

import sun.nio.ch.DirectBuffer;

class DirectCharBufferRU extends DirectCharBufferU implements DirectBuffer {
    /*synthetic*/ static final boolean $assertionsDisabled = !DirectCharBufferRU.class.desiredAssertionStatus();
    
    DirectCharBufferRU(DirectBuffer db, int mark, int pos, int lim, int cap, int off) {
        super(db, mark, pos, lim, cap, off);
    }
    
    public CharBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 1);
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new DirectCharBufferRU(this, -1, 0, rem, rem, off);
    }
    
    public CharBuffer duplicate() {
        return new DirectCharBufferRU(this, this.markValue(), this.position(), this.limit(), this.capacity(), 0);
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
    
    public CharBuffer put(CharBuffer src) {
        throw new ReadOnlyBufferException();
    }
    
    public CharBuffer put(char[] src, int offset, int length) {
        throw new ReadOnlyBufferException();
    }
    
    public CharBuffer compact() {
        throw new ReadOnlyBufferException();
    }
    
    public boolean isDirect() {
        return true;
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
        int off = (pos + start) << 1;
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new DirectCharBufferRU(this, -1, 0, sublen, sublen, off);
    }
    
    public ByteOrder order() {
        return ((ByteOrder.nativeOrder() != ByteOrder.BIG_ENDIAN) ? ByteOrder.LITTLE_ENDIAN : ByteOrder.BIG_ENDIAN);
    }
}
