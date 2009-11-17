package java.nio;

class HeapByteBufferR extends HeapByteBuffer {
    
    HeapByteBufferR(int cap, int lim) {
        super(cap, lim);
        this.isReadOnly = true;
    }
    
    HeapByteBufferR(byte[] buf, int off, int len) {
        super(buf, off, len);
        this.isReadOnly = true;
    }
    
    protected HeapByteBufferR(byte[] buf, int mark, int pos, int lim, int cap, int off) {
        super(buf, mark, pos, lim, cap, off);
        this.isReadOnly = true;
    }
    
    public ByteBuffer slice() {
        return new HeapByteBufferR(hb, -1, 0, this.remaining(), this.remaining(), this.position() + offset);
    }
    
    public ByteBuffer duplicate() {
        return new HeapByteBufferR(hb, this.markValue(), this.position(), this.limit(), this.capacity(), offset);
    }
    
    public ByteBuffer asReadOnlyBuffer() {
        return duplicate();
    }
    
    public boolean isReadOnly() {
        return true;
    }
    
    public ByteBuffer put(byte x) {
        throw new ReadOnlyBufferException();
    }
    
    public ByteBuffer put(int i, byte x) {
        throw new ReadOnlyBufferException();
    }
    
    public ByteBuffer put(byte[] src, int offset, int length) {
        throw new ReadOnlyBufferException();
    }
    
    public ByteBuffer put(ByteBuffer src) {
        throw new ReadOnlyBufferException();
    }
    
    public ByteBuffer compact() {
        throw new ReadOnlyBufferException();
    }
    
    byte _get(int i) {
        return hb[i];
    }
    
    void _put(int i, byte b) {
        throw new ReadOnlyBufferException();
    }
    
    public ByteBuffer putChar(char x) {
        throw new ReadOnlyBufferException();
    }
    
    public ByteBuffer putChar(int i, char x) {
        throw new ReadOnlyBufferException();
    }
    
    public CharBuffer asCharBuffer() {
        int size = this.remaining() >> 1;
        int off = offset + position();
        return (bigEndian ? (CharBuffer)(new ByteBufferAsCharBufferRB(this, -1, 0, size, size, off)) : (CharBuffer)(new ByteBufferAsCharBufferRL(this, -1, 0, size, size, off)));
    }
    
    public ByteBuffer putShort(short x) {
        throw new ReadOnlyBufferException();
    }
    
    public ByteBuffer putShort(int i, short x) {
        throw new ReadOnlyBufferException();
    }
    
    public ShortBuffer asShortBuffer() {
        int size = this.remaining() >> 1;
        int off = offset + position();
        return (bigEndian ? (ShortBuffer)(new ByteBufferAsShortBufferRB(this, -1, 0, size, size, off)) : (ShortBuffer)(new ByteBufferAsShortBufferRL(this, -1, 0, size, size, off)));
    }
    
    public ByteBuffer putInt(int x) {
        throw new ReadOnlyBufferException();
    }
    
    public ByteBuffer putInt(int i, int x) {
        throw new ReadOnlyBufferException();
    }
    
    public IntBuffer asIntBuffer() {
        int size = this.remaining() >> 2;
        int off = offset + position();
        return (bigEndian ? (IntBuffer)(new ByteBufferAsIntBufferRB(this, -1, 0, size, size, off)) : (IntBuffer)(new ByteBufferAsIntBufferRL(this, -1, 0, size, size, off)));
    }
    
    public ByteBuffer putLong(long x) {
        throw new ReadOnlyBufferException();
    }
    
    public ByteBuffer putLong(int i, long x) {
        throw new ReadOnlyBufferException();
    }
    
    public LongBuffer asLongBuffer() {
        int size = this.remaining() >> 3;
        int off = offset + position();
        return (bigEndian ? (LongBuffer)(new ByteBufferAsLongBufferRB(this, -1, 0, size, size, off)) : (LongBuffer)(new ByteBufferAsLongBufferRL(this, -1, 0, size, size, off)));
    }
    
    public ByteBuffer putFloat(float x) {
        throw new ReadOnlyBufferException();
    }
    
    public ByteBuffer putFloat(int i, float x) {
        throw new ReadOnlyBufferException();
    }
    
    public FloatBuffer asFloatBuffer() {
        int size = this.remaining() >> 2;
        int off = offset + position();
        return (bigEndian ? (FloatBuffer)(new ByteBufferAsFloatBufferRB(this, -1, 0, size, size, off)) : (FloatBuffer)(new ByteBufferAsFloatBufferRL(this, -1, 0, size, size, off)));
    }
    
    public ByteBuffer putDouble(double x) {
        throw new ReadOnlyBufferException();
    }
    
    public ByteBuffer putDouble(int i, double x) {
        throw new ReadOnlyBufferException();
    }
    
    public DoubleBuffer asDoubleBuffer() {
        int size = this.remaining() >> 3;
        int off = offset + position();
        return (bigEndian ? (DoubleBuffer)(new ByteBufferAsDoubleBufferRB(this, -1, 0, size, size, off)) : (DoubleBuffer)(new ByteBufferAsDoubleBufferRL(this, -1, 0, size, size, off)));
    }
}
