package java.nio;

public abstract class ByteBuffer extends Buffer implements Comparable {
    final byte[] hb;
    final int offset;
    boolean isReadOnly;
    
    ByteBuffer(int mark, int pos, int lim, int cap, byte[] hb, int offset) {
        super(mark, pos, lim, cap);
        this.hb = hb;
        this.offset = offset;
    }
    
    ByteBuffer(int mark, int pos, int lim, int cap) {
        this(mark, pos, lim, cap, null, 0);
    }
    
    public static ByteBuffer allocateDirect(int capacity) {
        return new DirectByteBuffer(capacity);
    }
    
    public static ByteBuffer allocate(int capacity) {
        if (capacity < 0) throw new IllegalArgumentException();
        return new HeapByteBuffer(capacity, capacity);
    }
    
    public static ByteBuffer wrap(byte[] array, int offset, int length) {
        try {
            return new HeapByteBuffer(array, offset, length);
        } catch (IllegalArgumentException x) {
            throw new IndexOutOfBoundsException();
        }
    }
    
    public static ByteBuffer wrap(byte[] array) {
        return wrap(array, 0, array.length);
    }
    
    public abstract ByteBuffer slice();
    
    public abstract ByteBuffer duplicate();
    
    public abstract ByteBuffer asReadOnlyBuffer();
    
    public abstract byte get();
    
    public abstract ByteBuffer put(byte b);
    
    public abstract byte get(int index);
    
    public abstract ByteBuffer put(int index, byte b);
    
    public ByteBuffer get(byte[] dst, int offset, int length) {
        checkBounds(offset, length, dst.length);
        if (length > remaining()) throw new BufferUnderflowException();
        int end = offset + length;
        for (int i = offset; i < end; i++) dst[i] = get();
        return this;
    }
    
    public ByteBuffer get(byte[] dst) {
        return get(dst, 0, dst.length);
    }
    
    public ByteBuffer put(ByteBuffer src) {
        if (src == this) throw new IllegalArgumentException();
        int n = src.remaining();
        if (n > remaining()) throw new BufferOverflowException();
        for (int i = 0; i < n; i++) put(src.get());
        return this;
    }
    
    public ByteBuffer put(byte[] src, int offset, int length) {
        checkBounds(offset, length, src.length);
        if (length > remaining()) throw new BufferOverflowException();
        int end = offset + length;
        for (int i = offset; i < end; i++) this.put(src[i]);
        return this;
    }
    
    public final ByteBuffer put(byte[] src) {
        return put(src, 0, src.length);
    }
    
    public final boolean hasArray() {
        return (hb != null) && !isReadOnly;
    }
    
    public final byte[] array() {
        if (hb == null) throw new UnsupportedOperationException();
        if (isReadOnly) throw new ReadOnlyBufferException();
        return hb;
    }
    
    public final int arrayOffset() {
        if (hb == null) throw new UnsupportedOperationException();
        if (isReadOnly) throw new ReadOnlyBufferException();
        return offset;
    }
    
    public abstract ByteBuffer compact();
    
    public abstract boolean isDirect();
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append(getClass().getName());
        sb.append("[pos=");
        sb.append(position());
        sb.append(" lim=");
        sb.append(limit());
        sb.append(" cap=");
        sb.append(capacity());
        sb.append("]");
        return sb.toString();
    }
    
    public int hashCode() {
        int h = 1;
        int p = position();
        for (int i = limit() - 1; i >= p; i--) h = 31 * h + (int)get(i);
        return h;
    }
    
    public boolean equals(Object ob) {
        if (!(ob instanceof ByteBuffer)) return false;
        ByteBuffer that = (ByteBuffer)(ByteBuffer)ob;
        if (this.remaining() != that.remaining()) return false;
        int p = this.position();
        for (int i = this.limit() - 1, j = that.limit() - 1; i >= p; i--, j--) {
            byte v1 = this.get(i);
            byte v2 = that.get(j);
            if (v1 != v2) {
                if ((v1 != v1) && (v2 != v2)) continue;
                return false;
            }
        }
        return true;
    }
    
    public int compareTo(ByteBuffer that) {
        int n = this.position() + Math.min(this.remaining(), that.remaining());
        for (int i = this.position(), j = that.position(); i < n; i++, j++) {
            byte v1 = this.get(i);
            byte v2 = that.get(j);
            if (v1 == v2) continue;
            if ((v1 != v1) && (v2 != v2)) continue;
            if (v1 < v2) return -1;
            return +1;
        }
        return this.remaining() - that.remaining();
    }
    boolean bigEndian = true;
    boolean nativeByteOrder = (Bits.byteOrder() == ByteOrder.BIG_ENDIAN);
    
    public final ByteOrder order() {
        return bigEndian ? ByteOrder.BIG_ENDIAN : ByteOrder.LITTLE_ENDIAN;
    }
    
    public final ByteBuffer order(ByteOrder bo) {
        bigEndian = (bo == ByteOrder.BIG_ENDIAN);
        nativeByteOrder = (bigEndian == (Bits.byteOrder() == ByteOrder.BIG_ENDIAN));
        return this;
    }
    
    abstract byte _get(int i);
    
    abstract void _put(int i, byte b);
    
    public abstract char getChar();
    
    public abstract ByteBuffer putChar(char value);
    
    public abstract char getChar(int index);
    
    public abstract ByteBuffer putChar(int index, char value);
    
    public abstract CharBuffer asCharBuffer();
    
    public abstract short getShort();
    
    public abstract ByteBuffer putShort(short value);
    
    public abstract short getShort(int index);
    
    public abstract ByteBuffer putShort(int index, short value);
    
    public abstract ShortBuffer asShortBuffer();
    
    public abstract int getInt();
    
    public abstract ByteBuffer putInt(int value);
    
    public abstract int getInt(int index);
    
    public abstract ByteBuffer putInt(int index, int value);
    
    public abstract IntBuffer asIntBuffer();
    
    public abstract long getLong();
    
    public abstract ByteBuffer putLong(long value);
    
    public abstract long getLong(int index);
    
    public abstract ByteBuffer putLong(int index, long value);
    
    public abstract LongBuffer asLongBuffer();
    
    public abstract float getFloat();
    
    public abstract ByteBuffer putFloat(float value);
    
    public abstract float getFloat(int index);
    
    public abstract ByteBuffer putFloat(int index, float value);
    
    public abstract FloatBuffer asFloatBuffer();
    
    public abstract double getDouble();
    
    public abstract ByteBuffer putDouble(double value);
    
    public abstract double getDouble(int index);
    
    public abstract ByteBuffer putDouble(int index, double value);
    
    public abstract DoubleBuffer asDoubleBuffer();
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((ByteBuffer)x0);
    }
}
