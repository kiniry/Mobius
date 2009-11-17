package java.nio.channels;

import java.io.IOException;
import java.net.DatagramSocket;
import java.net.SocketAddress;
import java.nio.ByteBuffer;
import java.nio.channels.spi.*;

public abstract class DatagramChannel extends AbstractSelectableChannel implements ByteChannel, ScatteringByteChannel, GatheringByteChannel {
    
    protected DatagramChannel(SelectorProvider provider) {
        super(provider);
    }
    
    public static DatagramChannel open() throws IOException {
        return SelectorProvider.provider().openDatagramChannel();
    }
    
    public final int validOps() {
        return (SelectionKey.OP_READ | SelectionKey.OP_WRITE);
    }
    
    public abstract DatagramSocket socket();
    
    public abstract boolean isConnected();
    
    public abstract DatagramChannel connect(SocketAddress remote) throws IOException;
    
    public abstract DatagramChannel disconnect() throws IOException;
    
    public abstract SocketAddress receive(ByteBuffer dst) throws IOException;
    
    public abstract int send(ByteBuffer src, SocketAddress target) throws IOException;
    
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
