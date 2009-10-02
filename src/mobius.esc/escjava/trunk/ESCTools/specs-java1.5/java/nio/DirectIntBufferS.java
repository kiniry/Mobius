package java.nio;

import sun.misc.Cleaner;
import sun.misc.Unsafe;
import sun.nio.ch.DirectBuffer;

class DirectIntBufferS extends IntBuffer implements DirectBuffer {
    /*synthetic*/ static final boolean $assertionsDisabled = !DirectIntBufferS.class.desiredAssertionStatus();
    protected static final Unsafe unsafe = Bits.unsafe();
    protected static final boolean unaligned = Bits.unaligned();
    protected Object viewedBuffer = null;
    
    public Object viewedBuffer() {
        return viewedBuffer;
    }
    
    public Cleaner cleaner() {
        return null;
    }
    
    DirectIntBufferS(DirectBuffer db, int mark, int pos, int lim, int cap, int off) {
        super(mark, pos, lim, cap);
        address = db.address() + off;
        viewedBuffer = db;
    }
    
    public IntBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 2);
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new DirectIntBufferS(this, -1, 0, rem, rem, off);
    }
    
    public IntBuffer duplicate() {
        return new DirectIntBufferS(this, this.markValue(), this.position(), this.limit(), this.capacity(), 0);
    }
    
    public IntBuffer asReadOnlyBuffer() {
        return new DirectIntBufferRS(this, this.markValue(), this.position(), this.limit(), this.capacity(), 0);
    }
    
    public long address() {
        return address;
    }
    
    private long ix(int i) {
        return address + (i << 2);
    }
    
    public int get() {
        return (Bits.swap(unsafe.getInt(ix(nextGetIndex()))));
    }
    
    public int get(int i) {
        return (Bits.swap(unsafe.getInt(ix(checkIndex(i)))));
    }
    
    public IntBuffer get(int[] dst, int offset, int length) {
        if ((length << 2) > Bits.JNI_COPY_TO_ARRAY_THRESHOLD) {
            checkBounds(offset, length, dst.length);
            int pos = position();
            int lim = limit();
            if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
            int rem = (pos <= lim ? lim - pos : 0);
            if (length > rem) throw new BufferUnderflowException();
            if (order() != ByteOrder.nativeOrder()) Bits.copyToIntArray(ix(pos), dst, offset << 2, length << 2); else Bits.copyToByteArray(ix(pos), dst, offset << 2, length << 2);
            position(pos + length);
        } else {
            super.get(dst, offset, length);
        }
        return this;
    }
    
    public IntBuffer put(int x) {
        unsafe.putInt(ix(nextPutIndex()), Bits.swap((x)));
        return this;
    }
    
    public IntBuffer put(int i, int x) {
        unsafe.putInt(ix(checkIndex(i)), Bits.swap((x)));
        return this;
    }
    
    public IntBuffer put(IntBuffer src) {
        if (src instanceof DirectIntBufferS) {
            if (src == this) throw new IllegalArgumentException();
            DirectIntBufferS sb = (DirectIntBufferS)(DirectIntBufferS)src;
            int spos = sb.position();
            int slim = sb.limit();
            if (!$assertionsDisabled && !(spos <= slim)) throw new AssertionError();
            int srem = (spos <= slim ? slim - spos : 0);
            int pos = position();
            int lim = limit();
            if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
            int rem = (pos <= lim ? lim - pos : 0);
            if (srem > rem) throw new BufferOverflowException();
            unsafe.copyMemory(sb.ix(spos), ix(pos), srem << 2);
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
    
    public IntBuffer put(int[] src, int offset, int length) {
        if ((length << 2) > Bits.JNI_COPY_FROM_ARRAY_THRESHOLD) {
            checkBounds(offset, length, src.length);
            int pos = position();
            int lim = limit();
            if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
            int rem = (pos <= lim ? lim - pos : 0);
            if (length > rem) throw new BufferOverflowException();
            if (order() != ByteOrder.nativeOrder()) Bits.copyFromIntArray(src, offset << 2, ix(pos), length << 2); else Bits.copyFromByteArray(src, offset << 2, ix(pos), length << 2);
            position(pos + length);
        } else {
            super.put(src, offset, length);
        }
        return this;
    }
    
    public IntBuffer compact() {
        int pos = position();
        int lim = limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        unsafe.copyMemory(ix(pos), ix(0), rem << 2);
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
