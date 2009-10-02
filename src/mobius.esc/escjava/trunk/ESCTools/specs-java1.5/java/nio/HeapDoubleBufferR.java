package java.nio;

class HeapDoubleBufferR extends HeapDoubleBuffer {
    
    HeapDoubleBufferR(int cap, int lim) {
        super(cap, lim);
        this.isReadOnly = true;
    }
    
    HeapDoubleBufferR(double[] buf, int off, int len) {
        super(buf, off, len);
        this.isReadOnly = true;
    }
    
    protected HeapDoubleBufferR(double[] buf, int mark, int pos, int lim, int cap, int off) {
        super(buf, mark, pos, lim, cap, off);
        this.isReadOnly = true;
    }
    
    public DoubleBuffer slice() {
        return new HeapDoubleBufferR(hb, -1, 0, this.remaining(), this.remaining(), this.position() + offset);
    }
    
    public DoubleBuffer duplicate() {
        return new HeapDoubleBufferR(hb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    public DoubleBuffer asReadOnlyBuffer() {
        return duplicate();
    }
    
    public boolean isReadOnly() {
        return true;
    }
    
    public DoubleBuffer put(double x) {
        throw new ReadOnlyBufferException();
    }
    
    public DoubleBuffer put(int i, double x) {
        throw new ReadOnlyBufferException();
    }
    
    public DoubleBuffer put(double[] src, int offset, int length) {
        throw new ReadOnlyBufferException();
    }
    
    public DoubleBuffer put(DoubleBuffer src) {
        throw new ReadOnlyBufferException();
    }
    
    public DoubleBuffer compact() {
        throw new ReadOnlyBufferException();
    }
    
    public ByteOrder order() {
        return ByteOrder.nativeOrder();
    }
}
