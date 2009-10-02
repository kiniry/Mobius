package java.nio.channels;

import java.io.IOException;
import java.net.ServerSocket;
import java.nio.channels.spi.*;

public abstract class ServerSocketChannel extends AbstractSelectableChannel {
    
    protected ServerSocketChannel(SelectorProvider provider) {
        super(provider);
    }
    
    public static ServerSocketChannel open() throws IOException {
        return SelectorProvider.provider().openServerSocketChannel();
    }
    
    public final int validOps() {
        return SelectionKey.OP_ACCEPT;
    }
    
    public abstract ServerSocket socket();
    
    public abstract SocketChannel accept() throws IOException;
}
