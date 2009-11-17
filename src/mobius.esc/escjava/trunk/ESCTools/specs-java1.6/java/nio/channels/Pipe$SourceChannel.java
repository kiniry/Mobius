package java.nio.channels;

import java.nio.channels.spi.*;

public abstract class Pipe$SourceChannel extends AbstractSelectableChannel implements ReadableByteChannel, ScatteringByteChannel {
    
    protected Pipe$SourceChannel(SelectorProvider provider) {
        super(provider);
    }
    
    public final int validOps() {
        return SelectionKey.OP_READ;
    }
}
