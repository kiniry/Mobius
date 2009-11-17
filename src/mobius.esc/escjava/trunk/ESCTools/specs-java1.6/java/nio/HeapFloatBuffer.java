package java.nio;

class HeapFloatBuffer extends FloatBuffer {
    
    HeapFloatBuffer(int cap, int lim) {
        super(-1, 0, lim, cap, new float[cap], 0);
    }
    
    HeapFloatBuffer(float[] buf, int off, int len) {
        super(-1, off, off + len, buf.length, buf, 0);
    }
    
    protected HeapFloatBuffer(float[] buf, int mark, int pos, int lim, int cap, int off) {
        super(mark, pos, lim, cap, buf, off);
    }
    
    public FloatBuffer slice() {
        return new HeapFloatBuffer(hb, -1, 0, this.remaining(), this.remaining(), this.position() + offset);
    }
    
    public FloatBuffer duplicate() {
        return new HeapFloatBuffer(hb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    public FloatBuffer asReadOnlyBuffer() {
        return new HeapFloatBufferR(hb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    protected int ix(int i) {
        return i + offset;
    }
    
    public float get() {
        return hb[ix(nextGetIndex())];
    }
    
    public float get(int i) {
        return hb[ix(checkIndex(i))];
    }
    
    public FloatBuffer get(float[] dst, int offset, int length) {
        checkBounds(offset, length, dst.length);
        if (length > remaining()) throw new BufferUnderflowException();
        System.arraycopy(hb, ix(position()), dst, offset, length);
        position(position() + length);
        return this;
    }
    
    public boolean isDirect() {
        return false;
    }
    
    public boolean isReadOnly() {
        return false;
    }
    
    public FloatBuffer put(float x) {
        hb[ix(nextPutIndex())] = x;
        return this;
    }
    
    public FloatBuffer put(int i, float x) {
        hb[ix(checkIndex(i))] = x;
        return this;
    }
    
    public FloatBuffer put(float[] src, int offset, int length) {
        checkBounds(offset, length, src.length);
        if (length > remaining()) throw new BufferOverflowException();
        System.arraycopy(src, offset, hb, ix(position()), length);
        position(position() + length);
        return this;
    }
    
    public FloatBuffer put(FloatBuffer src) {
        if (src instanceof HeapFloatBuffer) {
            if (src == this) throw new IllegalArgumentException();
            HeapFloatBuffer sb = (HeapFloatBuffer)(HeapFloatBuffer)src;
            int n = sb.remaining();
            if (n > remaining()) throw new BufferOverflowException();
            System.arraycopy(sb.hb, sb.ix(sb.position()), hb, ix(position()), n);
            sb.position(sb.position() + n);
            position(position() + n);
        } else if (src.isDirect()) {
            int n = src.remaining();
            if (n > remaining()) throw new BufferOverflowException();
            src.get(hb, ix(position()), n);
            position(position() + n);
        } else {
            super.put(src);
        }
        return this;
    }
    
    public FloatBuffer compact() {
        System.arraycopy(hb, ix(position()), hb, ix(0), remaining());
        position(remaining());
        limit(capacity());
        return this;
    }
    
    public ByteOrder order() {
        return ByteOrder.nativeOrder();
    }
}
