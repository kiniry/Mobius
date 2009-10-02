package java.nio;

class HeapFloatBufferR extends HeapFloatBuffer {
    
    HeapFloatBufferR(int cap, int lim) {
        super(cap, lim);
        this.isReadOnly = true;
    }
    
    HeapFloatBufferR(float[] buf, int off, int len) {
        super(buf, off, len);
        this.isReadOnly = true;
    }
    
    protected HeapFloatBufferR(float[] buf, int mark, int pos, int lim, int cap, int off) {
        super(buf, mark, pos, lim, cap, off);
        this.isReadOnly = true;
    }
    
    public FloatBuffer slice() {
        return new HeapFloatBufferR(hb, -1, 0, this.remaining(), this.remaining(), this.position() + offset);
    }
    
    public FloatBuffer duplicate() {
        return new HeapFloatBufferR(hb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    public FloatBuffer asReadOnlyBuffer() {
        return duplicate();
    }
    
    public boolean isReadOnly() {
        return true;
    }
    
    public FloatBuffer put(float x) {
        throw new ReadOnlyBufferException();
    }
    
    public FloatBuffer put(int i, float x) {
        throw new ReadOnlyBufferException();
    }
    
    public FloatBuffer put(float[] src, int offset, int length) {
        throw new ReadOnlyBufferException();
    }
    
    public FloatBuffer put(FloatBuffer src) {
        throw new ReadOnlyBufferException();
    }
    
    public FloatBuffer compact() {
        throw new ReadOnlyBufferException();
    }
    
    public ByteOrder order() {
        return ByteOrder.nativeOrder();
    }
}
