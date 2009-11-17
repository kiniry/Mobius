package java.nio.channels;

import java.io.*;
import java.nio.ByteBuffer;
import java.nio.MappedByteBuffer;
import java.nio.channels.spi.AbstractInterruptibleChannel;

public abstract class FileChannel extends AbstractInterruptibleChannel implements ByteChannel, GatheringByteChannel, ScatteringByteChannel {
    
    protected FileChannel() {
        
    }
    
    public abstract int read(ByteBuffer dst) throws IOException;
    
    public abstract long read(ByteBuffer[] dsts, int offset, int length) throws IOException;
    
    public final long read(ByteBuffer[] dsts) throws IOException {
        return read(dsts, 0, dsts.length);
    }
    
    public abstract int write(ByteBuffer src) throws IOException;
    
    public abstract long write(ByteBuffer[] srcs, int offset, int length) throws IOException;
    
    public final long write(ByteBuffer[] srcs) throws IOException {
        return write(srcs, 0, srcs.length);
    }
    
    public abstract long position() throws IOException;
    
    public abstract FileChannel position(long newPosition) throws IOException;
    
    public abstract long size() throws IOException;
    
    public abstract FileChannel truncate(long size) throws IOException;
    
    public abstract void force(boolean metaData) throws IOException;
    
    public abstract long transferTo(long position, long count, WritableByteChannel target) throws IOException;
    
    public abstract long transferFrom(ReadableByteChannel src, long position, long count) throws IOException;
    
    public abstract int read(ByteBuffer dst, long position) throws IOException;
    
    public abstract int write(ByteBuffer src, long position) throws IOException;
    {
    }
    
    public abstract MappedByteBuffer map(FileChannel$MapMode mode, long position, long size) throws IOException;
    
    public abstract FileLock lock(long position, long size, boolean shared) throws IOException;
    
    public final FileLock lock() throws IOException {
        return lock(0L, Long.MAX_VALUE, false);
    }
    
    public abstract FileLock tryLock(long position, long size, boolean shared) throws IOException;
    
    public final FileLock tryLock() throws IOException {
        return tryLock(0L, Long.MAX_VALUE, false);
    }
}
