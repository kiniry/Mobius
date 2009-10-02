package java.nio;

import sun.misc.Cleaner;
import sun.misc.Unsafe;
import sun.nio.ch.DirectBuffer;

class DirectDoubleBufferS extends DoubleBuffer implements DirectBuffer {
    /*synthetic*/ static final boolean $assertionsDisabled = !DirectDoubleBufferS.class.desiredAssertionStatus();
    protected static final Unsafe unsafe = Bits.unsafe();
    protected static final boolean unaligned = Bits.unaligned();
    protected Object viewedBuffer = null;
    
    public Object viewedBuffer() {
        return viewedBuffer;
    }
    
    public Cleaner cleaner() {
        return null;
    }
    
    DirectDoubleBufferS(DirectBuffer db, int mark, int pos, int lim, int cap, int off) {
        super(mark, pos, lim, cap);
        address = db.address() + off;
        viewedBuffer = db;
    }
    
    public DoubleBuffer slice() {
        int pos = this.position();
        int lim = this.limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        int off = (pos << 3);
        if (!$assertionsDisabled && !(off >= 0)) throw new AssertionError();
        return new DirectDoubleBufferS(this, -1, 0, rem, rem, off);
    }
    
    public DoubleBuffer duplicate() {
        return new DirectDoubleBufferS(this, this.markValue(), this.position(), this.limit(), this.capacity(), 0);
    }
    
    public DoubleBuffer asReadOnlyBuffer() {
        return new DirectDoubleBufferRS(this, this.markValue(), this.position(), this.limit(), this.capacity(), 0);
    }
    
    public long address() {
        return address;
    }
    
    private long ix(int i) {
        return address + (i << 3);
    }
    
    public double get() {
        return Double.longBitsToDouble(Bits.swap(unsafe.getLong(ix(nextGetIndex()))));
    }
    
    public double get(int i) {
        return Double.longBitsToDouble(Bits.swap(unsafe.getLong(ix(checkIndex(i)))));
    }
    
    public DoubleBuffer get(double[] dst, int offset, int length) {
        if ((length << 3) > Bits.JNI_COPY_TO_ARRAY_THRESHOLD) {
            checkBounds(offset, length, dst.length);
            int pos = position();
            int lim = limit();
            if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
            int rem = (pos <= lim ? lim - pos : 0);
            if (length > rem) throw new BufferUnderflowException();
            if (order() != ByteOrder.nativeOrder()) Bits.copyToLongArray(ix(pos), dst, offset << 3, length << 3); else Bits.copyToByteArray(ix(pos), dst, offset << 3, length << 3);
            position(pos + length);
        } else {
            super.get(dst, offset, length);
        }
        return this;
    }
    
    public DoubleBuffer put(double x) {
        unsafe.putLong(ix(nextPutIndex()), Bits.swap(Double.doubleToRawLongBits(x)));
        return this;
    }
    
    public DoubleBuffer put(int i, double x) {
        unsafe.putLong(ix(checkIndex(i)), Bits.swap(Double.doubleToRawLongBits(x)));
        return this;
    }
    
    public DoubleBuffer put(DoubleBuffer src) {
        if (src instanceof DirectDoubleBufferS) {
            if (src == this) throw new IllegalArgumentException();
            DirectDoubleBufferS sb = (DirectDoubleBufferS)(DirectDoubleBufferS)src;
            int spos = sb.position();
            int slim = sb.limit();
            if (!$assertionsDisabled && !(spos <= slim)) throw new AssertionError();
            int srem = (spos <= slim ? slim - spos : 0);
            int pos = position();
            int lim = limit();
            if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
            int rem = (pos <= lim ? lim - pos : 0);
            if (srem > rem) throw new BufferOverflowException();
            unsafe.copyMemory(sb.ix(spos), ix(pos), srem << 3);
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
    
    public DoubleBuffer put(double[] src, int offset, int length) {
        if ((length << 3) > Bits.JNI_COPY_FROM_ARRAY_THRESHOLD) {
            checkBounds(offset, length, src.length);
            int pos = position();
            int lim = limit();
            if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
            int rem = (pos <= lim ? lim - pos : 0);
            if (length > rem) throw new BufferOverflowException();
            if (order() != ByteOrder.nativeOrder()) Bits.copyFromLongArray(src, offset << 3, ix(pos), length << 3); else Bits.copyFromByteArray(src, offset << 3, ix(pos), length << 3);
            position(pos + length);
        } else {
            super.put(src, offset, length);
        }
        return this;
    }
    
    public DoubleBuffer compact() {
        int pos = position();
        int lim = limit();
        if (!$assertionsDisabled && !(pos <= lim)) throw new AssertionError();
        int rem = (pos <= lim ? lim - pos : 0);
        unsafe.copyMemory(ix(pos), ix(0), rem << 3);
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
