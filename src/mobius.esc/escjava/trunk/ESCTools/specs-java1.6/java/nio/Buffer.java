package java.nio;

public abstract class Buffer {
    private int mark = -1;
    private int position = 0;
    private int limit;
    private int capacity;
    long address;
    
    Buffer(int mark, int pos, int lim, int cap) {
        
        if (cap < 0) throw new IllegalArgumentException();
        this.capacity = cap;
        limit(lim);
        position(pos);
        if (mark >= 0) {
            if (mark > pos) throw new IllegalArgumentException();
            this.mark = mark;
        }
    }
    
    public final int capacity() {
        return capacity;
    }
    
    public final int position() {
        return position;
    }
    
    public final Buffer position(int newPosition) {
        if ((newPosition > limit) || (newPosition < 0)) throw new IllegalArgumentException();
        position = newPosition;
        if (mark > position) mark = -1;
        return this;
    }
    
    public final int limit() {
        return limit;
    }
    
    public final Buffer limit(int newLimit) {
        if ((newLimit > capacity) || (newLimit < 0)) throw new IllegalArgumentException();
        limit = newLimit;
        if (position > limit) position = limit;
        if (mark > limit) mark = -1;
        return this;
    }
    
    public final Buffer mark() {
        mark = position;
        return this;
    }
    
    public final Buffer reset() {
        int m = mark;
        if (m < 0) throw new InvalidMarkException();
        position = m;
        return this;
    }
    
    public final Buffer clear() {
        position = 0;
        limit = capacity;
        mark = -1;
        return this;
    }
    
    public final Buffer flip() {
        limit = position;
        position = 0;
        mark = -1;
        return this;
    }
    
    public final Buffer rewind() {
        position = 0;
        mark = -1;
        return this;
    }
    
    public final int remaining() {
        return limit - position;
    }
    
    public final boolean hasRemaining() {
        return position < limit;
    }
    
    public abstract boolean isReadOnly();
    
    final int nextGetIndex() {
        if (position >= limit) throw new BufferUnderflowException();
        return position++;
    }
    
    final int nextGetIndex(int nb) {
        if (limit - position < nb) throw new BufferUnderflowException();
        int p = position;
        position += nb;
        return p;
    }
    
    final int nextPutIndex() {
        if (position >= limit) throw new BufferOverflowException();
        return position++;
    }
    
    final int nextPutIndex(int nb) {
        if (limit - position < nb) throw new BufferOverflowException();
        int p = position;
        position += nb;
        return p;
    }
    
    final int checkIndex(int i) {
        if ((i < 0) || (i >= limit)) throw new IndexOutOfBoundsException();
        return i;
    }
    
    final int checkIndex(int i, int nb) {
        if ((i < 0) || (nb > limit - i)) throw new IndexOutOfBoundsException();
        return i;
    }
    
    final int markValue() {
        return mark;
    }
    
    static void checkBounds(int off, int len, int size) {
        if ((off | len | (off + len) | (size - (off + len))) < 0) throw new IndexOutOfBoundsException();
    }
}
