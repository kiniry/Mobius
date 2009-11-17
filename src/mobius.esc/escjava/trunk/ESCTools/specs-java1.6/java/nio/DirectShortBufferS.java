package java.nio;

import sun.misc.Cleaner;
import sun.misc.Unsafe;
import sun.nio.ch.DirectBuffer;

class DirectShortBufferS extends ShortBuffer implements DirectBuffer {
    /*synthetic*/ static final boolean $assertionsDisabled = !DirectShortBufferS.class.desiredAssertionStatus();
    protected static final Unsafe unsafe = Bits.unsafe();
    protected static final boolean unaligned = Bits.unaligned();
    protected Object viewedBuffer = null;
    
    public Object viewedBuffer() {
        return viewedBuffer;
    }
    
    public Cleaner cleaner() {
        return null;
    }
    
    DirectShortBufferS(DirectBuffer db, int mark, int pos, int lim, int cap, int off) {
        super(mark, pos, lim, cap);
        address = db.address() + off;
        viewedBuffer = db;
    }
    
    public ShortBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 1);
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new DirectShortBufferS(this, -1, 0, rem, rem, off);
    }
    
    public ShortBuffer duplicate() {
        return new DirectShortBufferS(this, this.markValue(), this.position(), this.limit(), this.capacity(), 0);
    }
    
    public ShortBuffer asReadOnlyBuffer() {
        return new DirectShortBufferRS(this, this.markValue(), this.position(), this.limit(), this.capacity(), 0);
    }
    
    public long address() {
        return address;
    }
    
    private long ix(int i) {
        return address + (i << 1);
    }
    
    public short get() {
        return (Bits.swap(unsafe.getShort(ix(nextGetIndex()))));
    }
    
    public short get(int i) {
        return (Bits.swap(unsafe.getShort(ix(checkIndex(i)))));
    }
    
    public ShortBuffer get(short[] dst, int offset, int length) {
        if ((length << 1) > Bits.JNI_COPY_TO_ARRAY_THRESHOLD) {
            checkBounds(offset, length, dst.length);
            int pos = position();
            int lim = limit();
            if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
            int rem = (pos <= lim ? lim - pos : 0);
            if (length > rem) throw new BufferUnderflowException();
            if (order() != ByteOrder.nativeOrder()) Bits.copyToShortArray(ix(pos), dst, offset << 1, length << 1); else Bits.copyToByteArray(ix(pos), dst, offset << 1, length << 1);
            position(pos + length);
        } else {
            super.get(dst, offset, length);
        }
        return this;
    }
    
    public ShortBuffer put(short x) {
        unsafe.putShort(ix(nextPutIndex()), Bits.swap((x)));
        return this;
    }
    
    public ShortBuffer put(int i, short x) {
        unsafe.putShort(ix(checkIndex(i)), Bits.swap((x)));
        return this;
    }
    
    public ShortBuffer put(ShortBuffer src) {
        if (src instanceof DirectShortBufferS) {
            if (src == this) throw new IllegalArgumentException();
            DirectShortBufferS sb = (DirectShortBufferS)(DirectShortBufferS)src;
            int spos = sb.position();
            int slim = sb.limit();
            if (!$assertionsDisabled && !(spos <= slim)) throw new AssertionError();
            int srem = (spos <= slim ? slim - spos : 0);
            int pos = position();
            int lim = limit();
            if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
            int rem = (pos <= lim ? lim - pos : 0);
            if (srem > rem) throw new BufferOverflowException();
            unsafe.copyMemory(sb.ix(spos), ix(pos), srem << 1);
            sb.position(spos + srem);
            position(pos + srem);
        } else if (!src.isDirect()) {
            int spos = src.position();
            int slim = src.limit();
            if (!$assertionsDisabled && !(spos <= slim)) throw new AssertionError();
            int srem = (spos <= slim ? slim - spos : 0);
            put(src.hb, src.offset + spos, srem);
            src.position(spos + srem);
        } else {
            super.put(src);
        }
        return this;
    }
    
    public ShortBuffer put(short[] src, int offset, int length) {
        if ((length << 1) > Bits.JNI_COPY_FROM_ARRAY_THRESHOLD) {
            checkBounds(offset, length, src.length);
            int pos = position();
            int lim = limit();
            if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
            int rem = (pos <= lim ? lim - pos : 0);
            if (length > rem) throw new BufferOverflowException();
            if (order() != ByteOrder.nativeOrder()) Bits.copyFromShortArray(src, offset << 1, ix(pos), length << 1); else Bits.copyFromByteArray(src, offset << 1, ix(pos), length << 1);
            position(pos + length);
        } else {
            super.put(src, offset, length);
        }
        return this;
    }
    
    public ShortBuffer compact() {
        int pos = position();
        int lim = limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        unsafe.copyMemory(ix(pos), ix(0), rem << 1);
        position(rem);
        limit(capacity());
        return this;
    }
    
    public boolean isDirect() {
        return true;
    }
    
    public boolean isReadOnly() {
        return false;
    }
    
    public ByteOrder order() {
        return ((ByteOrder.nativeOrder() == ByteOrder.BIG_ENDIAN) ? ByteOrder.LITTLE_ENDIAN : ByteOrder.BIG_ENDIAN);
    }
}
