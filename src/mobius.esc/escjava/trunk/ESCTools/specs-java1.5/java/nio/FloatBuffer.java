package java.nio;

public abstract class FloatBuffer extends Buffer implements Comparable {
    final float[] hb;
    final int offset;
    boolean isReadOnly;
    
    FloatBuffer(int mark, int pos, int lim, int cap, float[] hb, int offset) {
        super(mark, pos, lim, cap);
        this.hb = hb;
        this.offset = offset;
    }
    
    FloatBuffer(int mark, int pos, int lim, int cap) {
        this(mark, pos, lim, cap, null, 0);
    }
    
    public static FloatBuffer allocate(int capacity) {
        if (capacity < 0) throw new IllegalArgumentException();
        return new HeapFloatBuffer(capacity, capacity);
    }
    
    public static FloatBuffer wrap(float[] array, int offset, int length) {
        try {
            return new HeapFloatBuffer(array, offset, length);
        } catch (IllegalArgumentException x) {
            throw new IndexOutOfBoundsException();
        }
    }
    
    public static FloatBuffer wrap(float[] array) {
        return wrap(array, 0, array.length);
    }
    
    public abstract FloatBuffer slice();
    
    public abstract FloatBuffer duplicate();
    
    public abstract FloatBuffer asReadOnlyBuffer();
    
    public abstract float get();
    
    public abstract FloatBuffer put(float f);
    
    public abstract float get(int index);
    
    public abstract FloatBuffer put(int index, float f);
    
    public FloatBuffer get(float[] dst, int offset, int length) {
        checkBounds(offset, length, dst.length);
        if (length > remaining()) throw new BufferUnderflowException();
        int end = offset + length;
        for (int i = offset; i < end; i++) dst[i] = get();
        return this;
    }
    
    public FloatBuffer get(float[] dst) {
        return get(dst, 0, dst.length);
    }
    
    public FloatBuffer put(FloatBuffer src) {
        if (src == this) throw new IllegalArgumentException();
        int n = src.remaining();
        if (n > remaining()) throw new BufferOverflowException();
        for (int i = 0; i < n; i++) put(src.get());
        return this;
    }
    
    public FloatBuffer put(float[] src, int offset, int length) {
        checkBounds(offset, length, src.length);
        if (length > remaining()) throw new BufferOverflowException();
        int end = offset + length;
        for (int i = offset; i < end; i++) this.put(src[i]);
        return this;
    }
    
    public final FloatBuffer put(float[] src) {
        return put(src, 0, src.length);
    }
    
    public final boolean hasArray() {
        return (hb != null) && !isReadOnly;
    }
    
    public final float[] array() {
        if (hb == null) throw new UnsupportedOperationException();
        if (isReadOnly) throw new ReadOnlyBufferException();
        return hb;
    }
    
    public final int arrayOffset() {
        if (hb == null) throw new UnsupportedOperationException();
        if (isReadOnly) throw new ReadOnlyBufferException();
        return offset;
    }
    
    public abstract FloatBuffer compact();
    
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
        if (!(ob instanceof FloatBuffer)) return false;
        FloatBuffer that = (FloatBuffer)(FloatBuffer)ob;
        if (this.remaining() != that.remaining()) return false;
        int p = this.position();
        for (int i = this.limit() - 1, j = that.limit() - 1; i >= p; i--, j--) {
            float v1 = this.get(i);
            float v2 = that.get(j);
            if (v1 != v2) {
                if ((v1 != v1) && (v2 != v2)) continue;
                return false;
            }
        }
        return true;
    }
    
    public int compareTo(FloatBuffer that) {
        int n = this.position() + Math.min(this.remaining(), that.remaining());
        for (int i = this.position(), j = that.position(); i < n; i++, j++) {
            float v1 = this.get(i);
            float v2 = that.get(j);
            if (v1 == v2) continue;
            if ((v1 != v1) && (v2 != v2)) continue;
            if (v1 < v2) return -1;
            return +1;
        }
        return this.remaining() - that.remaining();
    }
    
    public abstract ByteOrder order();
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((FloatBuffer)x0);
    }
}
