package java.nio.channels;

import java.io.IOException;
import java.net.Socket;
import java.net.SocketAddress;
import java.nio.ByteBuffer;
import java.nio.channels.spi.*;

public abstract class SocketChannel extends AbstractSelectableChannel implements ByteChannel, ScatteringByteChannel, GatheringByteChannel {
    
    protected SocketChannel(SelectorProvider provider) {
        super(provider);
    }
    
    public static SocketChannel open() throws IOException {
        return SelectorProvider.provider().openSocketChannel();
    }
    
    public static SocketChannel open(SocketAddress remote) throws IOException {
        SocketChannel sc = open();
        sc.connect(remote);
        return sc;
    }
    
    public final int validOps() {
        return (SelectionKey.OP_READ | SelectionKey.OP_WRITE | SelectionKey.OP_CONNECT);
    }
    
    public abstract Socket socket();
    
    public abstract boolean isConnected();
    
    public abstract boolean isConnectionPending();
    
    public abstract boolean connect(SocketAddress remote) throws IOException;
    
    public abstract boolean finishConnect() throws IOException;
    
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
}
