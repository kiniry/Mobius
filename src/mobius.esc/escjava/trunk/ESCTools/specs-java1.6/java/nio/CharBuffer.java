package java.nio;

import java.io.IOException;

public abstract class CharBuffer extends Buffer implements Comparable, Appendable, CharSequence, Readable {
    final char[] hb;
    final int offset;
    boolean isReadOnly;
    
    CharBuffer(int mark, int pos, int lim, int cap, char[] hb, int offset) {
        super(mark, pos, lim, cap);
        this.hb = hb;
        this.offset = offset;
    }
    
    CharBuffer(int mark, int pos, int lim, int cap) {
        this(mark, pos, lim, cap, null, 0);
    }
    
    public static CharBuffer allocate(int capacity) {
        if (capacity < 0) throw new IllegalArgumentException();
        return new HeapCharBuffer(capacity, capacity);
    }
    
    public static CharBuffer wrap(char[] array, int offset, int length) {
        try {
            return new HeapCharBuffer(array, offset, length);
        } catch (IllegalArgumentException x) {
            throw new IndexOutOfBoundsException();
        }
    }
    
    public static CharBuffer wrap(char[] array) {
        return wrap(array, 0, array.length);
    }
    
    public int read(CharBuffer target) throws IOException {
        int targetRemaining = target.remaining();
        int remaining = remaining();
        if (remaining == 0) return -1;
        int n = Math.min(remaining, targetRemaining);
        int limit = limit();
        if (targetRemaining < remaining) limit(position() + n);
        try {
            if (n > 0) target.put(this);
        } finally {
            limit(limit);
        }
        return n;
    }
    
    public static CharBuffer wrap(CharSequence csq, int start, int end) {
        try {
            return new StringCharBuffer(csq, start, end);
        } catch (IllegalArgumentException x) {
            throw new IndexOutOfBoundsException();
        }
    }
    
    public static CharBuffer wrap(CharSequence csq) {
        return wrap(csq, 0, csq.length());
    }
    
    public abstract CharBuffer slice();
    
    public abstract CharBuffer duplicate();
    
    public abstract CharBuffer asReadOnlyBuffer();
    
    public abstract char get();
    
    public abstract CharBuffer put(char c);
    
    public abstract char get(int index);
    
    public abstract CharBuffer put(int index, char c);
    
    public CharBuffer get(char[] dst, int offset, int length) {
        checkBounds(offset, length, dst.length);
        if (length > remaining()) throw new BufferUnderflowException();
        int end = offset + length;
        for (int i = offset; i < end; i++) dst[i] = get();
        return this;
    }
    
    public CharBuffer get(char[] dst) {
        return get(dst, 0, dst.length);
    }
    
    public CharBuffer put(CharBuffer src) {
        if (src == this) throw new IllegalArgumentException();
        int n = src.remaining();
        if (n > remaining()) throw new BufferOverflowException();
        for (int i = 0; i < n; i++) put(src.get());
        return this;
    }
    
    public CharBuffer put(char[] src, int offset, int length) {
        checkBounds(offset, length, src.length);
        if (length > remaining()) throw new BufferOverflowException();
        int end = offset + length;
        for (int i = offset; i < end; i++) this.put(src[i]);
        return this;
    }
    
    public final CharBuffer put(char[] src) {
        return put(src, 0, src.length);
    }
    
    public CharBuffer put(String src, int start, int end) {
        checkBounds(start, end - start, src.length());
        for (int i = start; i < end; i++) this.put(src.charAt(i));
        return this;
    }
    
    public final CharBuffer put(String src) {
        return put(src, 0, src.length());
    }
    
    public final boolean hasArray() {
        return (hb != null) && !isReadOnly;
    }
    
    public final char[] array() {
        if (hb == null) throw new UnsupportedOperationException();
        if (isReadOnly) throw new ReadOnlyBufferException();
        return hb;
    }
    
    public final int arrayOffset() {
        if (hb == null) throw new UnsupportedOperationException();
        if (isReadOnly) throw new ReadOnlyBufferException();
        return offset;
    }
    
    public abstract CharBuffer compact();
    
    public abstract boolean isDirect();
    
    public int hashCode() {
        int h = 1;
        int p = position();
        for (int i = limit() - 1; i >= p; i--) h = 31 * h + (int)get(i);
        return h;
    }
    
    public boolean equals(Object ob) {
        if (!(ob instanceof CharBuffer)) return false;
        CharBuffer that = (CharBuffer)(CharBuffer)ob;
        if (this.remaining() != that.remaining()) return false;
        int p = this.position();
        for (int i = this.limit() - 1, j = that.limit() - 1; i >= p; i--, j--) {
            char v1 = this.get(i);
            char v2 = that.get(j);
            if (v1 != v2) {
                if ((v1 != v1) && (v2 != v2)) continue;
                return false;
            }
        }
        return true;
    }
    
    public int compareTo(CharBuffer that) {
        int n = this.position() + Math.min(this.remaining(), that.remaining());
        for (int i = this.position(), j = that.position(); i < n; i++, j++) {
            char v1 = this.get(i);
            char v2 = that.get(j);
            if (v1 == v2) continue;
            if ((v1 != v1) && (v2 != v2)) continue;
            if (v1 < v2) return -1;
            return +1;
        }
        return this.remaining() - that.remaining();
    }
    
    public String toString() {
        return toString(position(), limit());
    }
    
    abstract String toString(int start, int end);
    
    public final int length() {
        return remaining();
    }
    
    public final char charAt(int index) {
        return get(position() + checkIndex(index, 1));
    }
    
    public abstract CharSequence subSequence(int start, int end);
    
    public CharBuffer append(CharSequence csq) {
        if (csq == null) return put("null"); else return put(csq.toString());
    }
    
    public CharBuffer append(CharSequence csq, int start, int end) {
        CharSequence cs = (csq == null ? "null" : csq);
        return put(cs.subSequence(start, end).toString());
    }
    
    public CharBuffer append(char c) {
        return put(c);
    }
    
    public abstract ByteOrder order();
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((CharBuffer)x0);
    }
    
    /*synthetic public Appendable append(char x0) throws IOException {
        return this.append(x0);
    }*/
    
    /*synthetic public Appendable append(CharSequence x0, int x1, int x2) throws IOException {
        return this.append(x0, x1, x2);
    }*/
    
    /*synthetic public Appendable append(CharSequence x0) throws IOException {
        return this.append(x0);
    } */
}
