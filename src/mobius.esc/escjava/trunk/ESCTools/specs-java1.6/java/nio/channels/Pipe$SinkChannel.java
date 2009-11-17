package java.nio.channels;

import java.nio.channels.spi.*;

public abstract class Pipe$SinkChannel extends AbstractSelectableChannel implements WritableByteChannel, GatheringByteChannel {
    
    protected Pipe$SinkChannel(SelectorProvider provider) {
        super(provider);
    }
    
    public final int validOps() {
        return SelectionKey.OP_WRITE;
    }
}
