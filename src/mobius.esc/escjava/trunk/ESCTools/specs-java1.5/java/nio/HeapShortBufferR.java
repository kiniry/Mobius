package java.nio;

class HeapShortBufferR extends HeapShortBuffer {
    
    HeapShortBufferR(int cap, int lim) {
        super(cap, lim);
        this.isReadOnly = true;
    }
    
    HeapShortBufferR(short[] buf, int off, int len) {
        super(buf, off, len);
        this.isReadOnly = true;
    }
    
    protected HeapShortBufferR(short[] buf, int mark, int pos, int lim, int cap, int off) {
        super(buf, mark, pos, lim, cap, off);
        this.isReadOnly = true;
    }
    
    public ShortBuffer slice() {
        return new HeapShortBufferR(hb, -1, 0, this.remaining(), this.remaining(), this.position() + offset);
    }
    
    public ShortBuffer duplicate() {
        return new HeapShortBufferR(hb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    public ShortBuffer asReadOnlyBuffer() {
        return duplicate();
    }
    
    public boolean isReadOnly() {
        return true;
    }
    
    public ShortBuffer put(short x) {
        throw new ReadOnlyBufferException();
    }
    
    public ShortBuffer put(int i, short x) {
        throw new ReadOnlyBufferException();
    }
    
    public ShortBuffer put(short[] src, int offset, int length) {
        throw new ReadOnlyBufferException();
    }
    
    public ShortBuffer put(ShortBuffer src) {
        throw new ReadOnlyBufferException();
    }
    
    public ShortBuffer compact() {
        throw new ReadOnlyBufferException();
    }
    
    public ByteOrder order() {
        return ByteOrder.nativeOrder();
    }
}
