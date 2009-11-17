package java.nio;

public abstract class LongBuffer extends Buffer implements Comparable {
    final long[] hb;
    final int offset;
    boolean isReadOnly;
    
    LongBuffer(int mark, int pos, int lim, int cap, long[] hb, int offset) {
        super(mark, pos, lim, cap);
        this.hb = hb;
        this.offset = offset;
    }
    
    LongBuffer(int mark, int pos, int lim, int cap) {
        this(mark, pos, lim, cap, null, 0);
    }
    
    public static LongBuffer allocate(int capacity) {
        if (capacity < 0) throw new IllegalArgumentException();
        return new HeapLongBuffer(capacity, capacity);
    }
    
    public static LongBuffer wrap(long[] array, int offset, int length) {
        try {
            return new HeapLongBuffer(array, offset, length);
        } catch (IllegalArgumentException x) {
            throw new IndexOutOfBoundsException();
        }
    }
    
    public static LongBuffer wrap(long[] array) {
        return wrap(array, 0, array.length);
    }
    
    public abstract LongBuffer slice();
    
    public abstract LongBuffer duplicate();
    
    public abstract LongBuffer asReadOnlyBuffer();
    
    public abstract long get();
    
    public abstract LongBuffer put(long l);
    
    public abstract long get(int index);
    
    public abstract LongBuffer put(int index, long l);
    
    public LongBuffer get(long[] dst, int offset, int length) {
        checkBounds(offset, length, dst.length);
        if (length > remaining()) throw new BufferUnderflowException();
        int end = offset + length;
        for (int i = offset; i < end; i++) dst[i] = get();
        return this;
    }
    
    public LongBuffer get(long[] dst) {
        return get(dst, 0, dst.length);
    }
    
    public LongBuffer put(LongBuffer src) {
        if (src == this) throw new IllegalArgumentException();
        int n = src.remaining();
        if (n > remaining()) throw new BufferOverflowException();
        for (int i = 0; i < n; i++) put(src.get());
        return this;
    }
    
    public LongBuffer put(long[] src, int offset, int length) {
        checkBounds(offset, length, src.length);
        if (length > remaining()) throw new BufferOverflowException();
        int end = offset + length;
        for (int i = offset; i < end; i++) this.put(src[i]);
        return this;
    }
    
    public final LongBuffer put(long[] src) {
        return put(src, 0, src.length);
    }
    
    public final boolean hasArray() {
        return (hb != null) && !isReadOnly;
    }
    
    public final long[] array() {
        if (hb == null) throw new UnsupportedOperationException();
        if (isReadOnly) throw new ReadOnlyBufferException();
        return hb;
    }
    
    public final int arrayOffset() {
        if (hb == null) throw new UnsupportedOperationException();
        if (isReadOnly) throw new ReadOnlyBufferException();
        return offset;
    }
    
    public abstract LongBuffer compact();
    
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
        if (!(ob instanceof LongBuffer)) return false;
        LongBuffer that = (LongBuffer)(LongBuffer)ob;
        if (this.remaining() != that.remaining()) return false;
        int p = this.position();
        for (int i = this.limit() - 1, j = that.limit() - 1; i >= p; i--, j--) {
            long v1 = this.get(i);
            long v2 = that.get(j);
            if (v1 != v2) {
                if ((v1 != v1) && (v2 != v2)) continue;
                return false;
            }
        }
        return true;
    }
    
    public int compareTo(LongBuffer that) {
        int n = this.position() + Math.min(this.remaining(), that.remaining());
        for (int i = this.position(), j = that.position(); i < n; i++, j++) {
            long v1 = this.get(i);
            long v2 = that.get(j);
            if (v1 == v2) continue;
            if ((v1 != v1) && (v2 != v2)) continue;
            if (v1 < v2) return -1;
            return +1;
        }
        return this.remaining() - that.remaining();
    }
    
    public abstract ByteOrder order();
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((LongBuffer)x0);
    }
}
