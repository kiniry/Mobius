package java.nio;

public abstract class MappedByteBuffer extends ByteBuffer {
    volatile boolean isAMappedBuffer;
    
    MappedByteBuffer(int mark, int pos, int lim, int cap, boolean mapped) {
        super(mark, pos, lim, cap);
        isAMappedBuffer = mapped;
    }
    
    MappedByteBuffer(int mark, int pos, int lim, int cap) {
        super(mark, pos, lim, cap);
        isAMappedBuffer = false;
    }
    
    private void checkMapped() {
        if (!isAMappedBuffer) throw new UnsupportedOperationException();
    }
    
    public final boolean isLoaded() {
        checkMapped();
        if ((address == 0) || (capacity() == 0)) return true;
        return isLoaded0(((DirectByteBuffer)(DirectByteBuffer)this).address(), capacity());
    }
    
    public final MappedByteBuffer load() {
        checkMapped();
        if ((address == 0) || (capacity() == 0)) return this;
        load0(((DirectByteBuffer)(DirectByteBuffer)this).address(), capacity(), Bits.pageSize());
        return this;
    }
    
    public final MappedByteBuffer force() {
        checkMapped();
        if ((address == 0) || (capacity() == 0)) return this;
        force0(((DirectByteBuffer)(DirectByteBuffer)this).address(), capacity());
        return this;
    }
    
    private native boolean isLoaded0(long address, long length);
    
    private native int load0(long address, long length, int pageSize);
    
    private native void force0(long address, long length);
}
